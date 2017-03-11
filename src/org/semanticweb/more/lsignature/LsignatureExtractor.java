package org.semanticweb.more.lsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.more.BottomLocalityChecker;
import org.semanticweb.more.ListProcessor;
import org.semanticweb.more.LocalityInfo;
import org.semanticweb.more.io.LogOutput;
import org.semanticweb.more.visitors.ELKAxiomVisitor;
import org.semanticweb.more.visitors.OWLFragmentVisitor;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;

public class LsignatureExtractor {

	protected Fragment fragment;
	protected OWLOntology ontology;
	protected Set<OWLEntity> lSignature;
	protected Set<OWLEntity> compSignature;
	protected Set<OWLClass> classesInvisibleInL;
	protected Set<OWLAxiom> lSignatureModule;// this may contain axioms that are
												// local wrt the lSignature but
												// which contain no entity
												// outside the lSignature

	protected BottomLocalityChecker localityChecker = new BottomLocalityChecker(
			true);

	protected boolean printAxiomsNotInFragment;

	public LsignatureExtractor(boolean printAxNotInFragment) {
		printAxiomsNotInFragment = printAxNotInFragment;
	}

	public LsignatureExtractor() {
		this(false);
		// this(true);
	}

	public Set<OWLEntity> getLsignature() {
		return lSignature;
	}

	public Set<OWLEntity> getCompSignature() {
		return compSignature;
	}

	public Set<OWLAxiom> getLsignatureModule() {
		return lSignatureModule;
	}

	public Set<OWLClass> getClassesInvisibleInL() {
		return classesInvisibleInL;
	}

	public Set<OWLEntity> findLsignature(OWLOntology o, Fragment f) {
		ontology = o;
		fragment = f;

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

				LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom,
						compSignature);
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
				LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom,
						lSignature);// did I break something by moving this in
									// here?
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

	protected OWLFragmentVisitor getFragmentVisitor() {
		switch (fragment) {
		case ELK:
			return new ELKAxiomVisitor();
			// case HornSHIF:
			// return new HornSHIFAxiomVisitor();
			// case OWL2EL:
			// return new ELAxiomVisitor();
		default:
			System.out.println("Fragment not implemented");
			return null;
		}

	}

	public void resetValues() { // better way of doing this?
		fragment = null;
		ontology = null;
		lSignature = null;
		compSignature = null;
		classesInvisibleInL = null;
		lSignatureModule = null;
	}

	public enum Fragment {
		ELK, HornSHIF, OWL2EL
	}

}
