package org.semanticweb.more.lsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.more.ListProcessor;
import org.semanticweb.more.LocalityInfo;
import org.semanticweb.more.io.LogOutput;
import org.semanticweb.more.visitors.OWLFragmentVisitor;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class ImprovedLsignatureExtractor extends LsignatureExtractor {

	protected Set<OWLEntity> globalEntities;// we keep track of entities which
											// can't possibly be removed from
											// the Lsignature without making it
											// empty in order to improve our
											// heuristics

	protected ImprovedBottomLocalityChecker locChecker = new ImprovedBottomLocalityChecker();

	@Override
	public Set<OWLEntity> findLsignature(OWLOntology o, Fragment f) {
		ontology = o;
		fragment = f;
		findGlobalEntities();

		long tExt = System.currentTimeMillis();
		initialiseLsignature();
		int currentSize = lSignature.size();
		int previousSize = 0;
		while (currentSize != previousSize) {
			reduceLsignature();
			previousSize = currentSize;
			currentSize = lSignature.size();
		}
		tExt = System.currentTimeMillis() - tExt;
		LogOutput.print("Lsignature extraction took " + tExt + " milliseconds");// and
																				// "+ nIterations + "
																				// iterations");
		LogOutput.print("Lsignature of size " + lSignature.size());

		return lSignature;
	}

	@Override
	protected void initialiseLsignature() {

		LinkedList<List<Set<OWLEntity>>> solutionsForAllAxioms = new LinkedList<List<Set<OWLEntity>>>();
		OWLFragmentVisitor fragmentVisitor = getFragmentVisitor();

		compSignature = ontology.getSignature();
		lSignatureModule = new HashSet<OWLAxiom>();
		classesInvisibleInL = ontology.getClassesInSignature();

		for (OWLAxiom axiom : ontology.getAxioms()) {
			axiom.accept(fragmentVisitor);
			if (fragmentVisitor.isInFragment()) {
				lSignatureModule.add(axiom);
				classesInvisibleInL.removeAll(axiom.getClassesInSignature());
			} else {

				if (printAxiomsNotInFragment)
					System.out.println(axiom.toString() + " not in fragment "
							+ fragment.toString());

				LocalityInfo locInfo = locChecker.isLocalAxiom(axiom,
						compSignature, globalEntities);
				if (!locInfo.is()) {
					if (locInfo.canMake()) {
						// List<Set<OWLEntity>> solutionsForSomeAxiom =
						// locInfo.getSolutions();
						if (locInfo.getSolutions().size() == 1)
							solutionsForAllAxioms.addFirst(locInfo
									.getSolutions());
						else
							solutionsForAllAxioms.add(locInfo.getSolutions());
					} else {
						System.out.println("empty lSignature due to axiom "
								+ axiom.toString());
						lSignature = new HashSet<OWLEntity>(); // and in this
																// case
																// compSignature
																// stays with
																// its current
																// value of
																// ontology.getSignature()
						lSignatureModule = new HashSet<OWLAxiom>();
						return;
					}
				}
			}
		}

		lSignature = compSignature;// compSignature still contains the whole
									// signature
		compSignature = new ListProcessor().getMinimalCombination(
				solutionsForAllAxioms, compSignature.size());
		lSignature.removeAll(compSignature);
	}

	protected void reduceLsignature() {
		Set<OWLAxiom> newLocalAxioms = new HashSet<OWLAxiom>();
		LinkedList<List<Set<OWLEntity>>> solutionsForAllAxioms = new LinkedList<List<Set<OWLEntity>>>();

		for (OWLAxiom axiom : lSignatureModule) {
			// LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom,
			// lSignature);
			if (!lSignature.containsAll(axiom.getSignature())) {
				LocalityInfo locInfo = locChecker.isLocalAxiom(axiom,
						lSignature, globalEntities);// did I break something by
													// moving this in here?
				if (!locInfo.is())
					if (locInfo.canMake()) {

						// List<Set<OWLEntity>> solutionsForSomeAxiom =
						// locInfo.getSolutions();
						if (locInfo.getSolutions().size() == 1)
							solutionsForAllAxioms.addFirst(locInfo
									.getSolutions());
						else
							solutionsForAllAxioms.add(locInfo.getSolutions());

						newLocalAxioms.add(axiom);

					} else {
						System.out.println("empty lSignature due to axiom "
								+ axiom.toString());
						lSignature = new HashSet<OWLEntity>();
						compSignature = ontology.getSignature();
						lSignatureModule = new HashSet<OWLAxiom>();
						return;
					}
			}
		}

		Set<OWLEntity> notInLsignature = new ListProcessor()
				.getMinimalCombination(solutionsForAllAxioms, lSignature.size());
		compSignature.addAll(notInLsignature);
		lSignature.removeAll(notInLsignature);
		lSignatureModule.removeAll(newLocalAxioms);
	}

	protected void findGlobalEntities() {

		Set<OWLAxiom> notGlobalAxioms = new HashSet<OWLAxiom>(
				ontology.getAxioms());
		Set<OWLAxiom> globalAxioms = new HashSet<OWLAxiom>();

		globalEntities = new HashSet<OWLEntity>();
		for (OWLAxiom ax : notGlobalAxioms) {

			// might be worth checking all axioms in this loop? there might be
			// other kinds of axioms that can be made local...

			if (ax instanceof OWLSubClassOfAxiom) {
				// OWLSubClassOfAxiom scax = (OWLSubClassOfAxiom) ax;
				OWLClassExpression subClass = ((OWLSubClassOfAxiom) ax)
						.getSubClass();
				if (subClass.equals(new OWLDataFactoryImpl().getOWLThing())
						|| subClass instanceof OWLObjectAllValuesFrom) {
					if (!locChecker.isLocalAxiom(ax, ax.getSignature(),
							new HashSet<OWLEntity>()).canMake()) {
						globalEntities.addAll(ax.getSignature());
						globalAxioms.add(ax);
					}
				}
			}
		}
		notGlobalAxioms.removeAll(globalAxioms);
		Set<OWLEntity> newGlobalEntities = new HashSet<OWLEntity>(
				globalEntities);
		while (!newGlobalEntities.isEmpty()) {
			Set<OWLEntity> aux = new HashSet<OWLEntity>(newGlobalEntities);
			newGlobalEntities.clear();
			for (OWLAxiom ax : notGlobalAxioms) {
				if (containsGlobalEntities(ax, aux)) {
					if (!locChecker.isLocalAxiom(ax, new HashSet<OWLEntity>(),
							globalEntities).canMake()) {
						globalAxioms.add(ax);
						newGlobalEntities.addAll(ax.getSignature());
					}
				}
			}

			notGlobalAxioms.removeAll(globalAxioms);
			newGlobalEntities.removeAll(globalEntities);
			globalEntities.addAll(newGlobalEntities);
		}
	}

	private boolean containsGlobalEntities(OWLAxiom ax,
			Set<OWLEntity> globalEnts) {
		Set<OWLEntity> intersection = new HashSet<OWLEntity>(ax.getSignature());
		intersection.retainAll(globalEnts);
		return !intersection.isEmpty();
	}
}
