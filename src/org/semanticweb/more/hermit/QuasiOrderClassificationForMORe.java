package org.semanticweb.more.hermit;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import org.semanticweb.HermiT.graph.Graph;
import org.semanticweb.HermiT.hierarchy.ClassificationProgressMonitor;
import org.semanticweb.HermiT.hierarchy.Hierarchy;
import org.semanticweb.HermiT.hierarchy.HierarchyNode;
import org.semanticweb.HermiT.hierarchy.HierarchySearch.Relation;
import org.semanticweb.HermiT.hierarchy.QuasiOrderClassification;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.tableau.Tableau;

public class QuasiOrderClassificationForMORe extends QuasiOrderClassification {

	public QuasiOrderClassificationForMORe(Tableau tableau,
			ClassificationProgressMonitor progressMonitor,
			AtomicConcept topElement, AtomicConcept bottomElement,
			Set<AtomicConcept> elements,
			Graph<AtomicConcept> possibleSubsumptions,
			Graph<AtomicConcept> knownSubsumtions) {
		super(tableau, progressMonitor, topElement, bottomElement, elements);
		for (AtomicConcept ac : elements)
			// upperBound.getElements())
			for (AtomicConcept candidateSubsumer : possibleSubsumptions
					.getSuccessors(ac))
				addPossibleSubsumption(ac, candidateSubsumer);
		for (AtomicConcept ac : knownSubsumtions.getElements())
			for (AtomicConcept subsumer : knownSubsumtions.getSuccessors(ac))
				addKnownSubsumption(ac, subsumer);
	}

	@Override
	protected double updateSubsumptionsUsingLeafNodeStrategy(
			double totalNumberOfTasks) {
		double conceptsProcessed = 0;
		Hierarchy<AtomicConcept> hierarchy = buildTransitivelyReducedHierarchy(
				m_knownSubsumptions, m_elements);
		Stack<HierarchyNode<AtomicConcept>> toProcess = new Stack<HierarchyNode<AtomicConcept>>();
		toProcess.addAll(hierarchy.getBottomNode().getParentNodes());
		while (!toProcess.empty()) {
			HierarchyNode<AtomicConcept> currentHierarchyElement = toProcess
					.pop();
			AtomicConcept currentHierarchyConcept = currentHierarchyElement
					.getRepresentative();
			if (conceptsProcessed < Math.ceil(totalNumberOfTasks * 0.85)) {
				m_progressMonitor.elementClassified(currentHierarchyConcept);
				conceptsProcessed++;
			}
		}
		return conceptsProcessed;
	}

	@Override
	protected Hierarchy<AtomicConcept> buildHierarchy(
			Relation<AtomicConcept> hierarchyRelation) {
		double totalNumberOfTasks = m_elements.size();
		makeConceptUnsatisfiable(m_bottomElement);
		initialiseKnownSubsumptionsUsingToldSubsumers();

		long t = System.currentTimeMillis();

		double tasksPerformed = updateSubsumptionsUsingLeafNodeStrategy(totalNumberOfTasks);

		// t = System.currentTimeMillis() - t;
		// System.out.println(t +
		// " milliseconds for QuasiOrderClassification.updateSubsumptionsUsingLeafNodeStrategy and removing "
		// +
		// "redundant possiblesubsumptions in  " +
		// "QuasiOrderClassification.buildHierarchy");

		// Unlike Rob's paper our set of possible subsumptions P would only keep
		// unknown possible subsumptions and not known subsumptions as well.
		Set<AtomicConcept> unclassifiedElements = new HashSet<AtomicConcept>();
		for (AtomicConcept element : m_elements) {
			if (!isUnsatisfiable(element)) {
				m_possibleSubsumptions.getSuccessors(element).removeAll(
						getAllKnownSubsumers(element));
				if (!m_possibleSubsumptions.getSuccessors(element).isEmpty()) {
					unclassifiedElements.add(element);
					continue;
				}
			}
		}

		// ------------------------------------
		t = System.currentTimeMillis() - t;

		// and now let's see how the P and K sets have been initialised
		int possibleSubsumptions = 0;
		for (AtomicConcept ac : m_possibleSubsumptions.getElements()) {
			// System.out.println(ac.toString() + " " +
			// m_possibleSubsumptions.getReachableSuccessors(ac).size());
			possibleSubsumptions = possibleSubsumptions
					+ m_possibleSubsumptions.getReachableSuccessors(ac).size();
		}
		// System.out.println("there are " +
		// m_possibleSubsumptions.getElements().size() +
		// " nodes in m_possibleSubsumptions");
		// System.out.println("there are " + possibleSubsumptions +
		// " possible subsumptions");

		int knownSubsumptions = 0;
		for (AtomicConcept ac : m_knownSubsumptions.getElements()) {
			// System.out.println(ac.toString() + " " +
			// m_knownSubsumptions.getReachableSuccessors(ac).size());
			knownSubsumptions = knownSubsumptions
					+ m_knownSubsumptions.getReachableSuccessors(ac).size();
		}
		// System.out.println("there are " +
		// m_knownSubsumptions.getElements().size() +
		// " nodes in m_knownSubsumptions");
		// System.out.println("there are " + knownSubsumptions +
		// " known subsumptions");
		//
		// System.out.println(unclassifiedElements.size() +
		// " unclassified elements after intialisation");

		long tForUnclassifiedConcepts = 0;
		int nProcessedConcepts = 0;
		// ------------------------------------

		Set<AtomicConcept> classifiedElements = new HashSet<AtomicConcept>();
		while (!unclassifiedElements.isEmpty()) {

			// //--------
			// System.out.println(unclassifiedElements.size());
			// //--------

			AtomicConcept unclassifiedElement = null;
			for (AtomicConcept element : unclassifiedElements) {
				m_possibleSubsumptions.getSuccessors(element).removeAll(
						getAllKnownSubsumers(element));
				if (!m_possibleSubsumptions.getSuccessors(element).isEmpty()) {
					unclassifiedElement = element;
					break;
				}
				classifiedElements.add(element);
				while (unclassifiedElements.size() < (totalNumberOfTasks - tasksPerformed)) {
					m_progressMonitor.elementClassified(element);
					tasksPerformed++;
				}
			}
			unclassifiedElements.removeAll(classifiedElements);
			if (unclassifiedElements.isEmpty())
				break;

			// -----------------------------------------
			long tt = System.currentTimeMillis();
			// -----------------------------------------

			Set<AtomicConcept> unknownPossibleSubsumers = m_possibleSubsumptions
					.getSuccessors(unclassifiedElement);
			if (!isEveryPossibleSubsumerNonSubsumer(unknownPossibleSubsumers,
					unclassifiedElement, 2, 7)
					&& !unknownPossibleSubsumers.isEmpty()) {
				Hierarchy<AtomicConcept> smallHierarchy = buildHierarchyOfUnknownPossible(unknownPossibleSubsumers);
				checkUnknownSubsumersUsingEnhancedTraversal(hierarchyRelation,
						smallHierarchy.getTopNode(), unclassifiedElement);
			}

			// -----------------------------------------
			tt = System.currentTimeMillis() - tt;
			// if (tt > 16)
			// System.out.println(tt + " milliseconds to process " +
			// unclassifiedElement.toString());

			tForUnclassifiedConcepts = tForUnclassifiedConcepts + tt;
			nProcessedConcepts++;

			unknownPossibleSubsumers.clear();
			// -----------------------------------------
		}

		// System.out.println("in the end only " + nProcessedConcepts +
		// " concepts needed to be processed directly");

		return buildTransitivelyReducedHierarchy(m_knownSubsumptions,
				m_elements);
	}
}
