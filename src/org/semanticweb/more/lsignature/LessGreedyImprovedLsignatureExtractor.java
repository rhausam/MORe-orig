package org.semanticweb.more.lsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.more.ListProcessor;
import org.semanticweb.more.LocalityInfo;
import org.semanticweb.more.io.LogOutput;
import org.semanticweb.more.visitors.OWLFragmentVisitor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

public class LessGreedyImprovedLsignatureExtractor extends
		ImprovedLsignatureExtractor {

	// protected Set<OWLEntity> globalEntities;
	protected Set<OWLAxiom> nonFragmentAxiomsStillNonLocal = new HashSet<OWLAxiom>();

	// protected ImprovedBottomLocalityChecker locChecker = new
	// ImprovedBottomLocalityChecker();

	protected SyntacticLocalityModuleExtractor moduleExtractor;
	OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

	public Set<OWLEntity> findLsignature(OWLOntology o, Fragment f) {
		ontology = o;
		fragment = f;

		findGlobalEntities();

		moduleExtractor = new SyntacticLocalityModuleExtractor(manager,
				ontology, ModuleType.BOT);

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

		LinkedList<List<Set<OWLEntity>>> nondeterministicSolutions = new LinkedList<List<Set<OWLEntity>>>();

		OWLFragmentVisitor fragmentVisitor = getFragmentVisitor();

		lSignature = ontology.getSignature();
		compSignature = new HashSet<OWLEntity>();
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
						lSignature, globalEntities);
				if (!locInfo.is()) {
					if (locInfo.canMake()) {
						if (locInfo.getSolutions().size() == 1)
							// actually some kind of greedyness may have been
							// applied laready in constructing this, so this is
							// not guaramteed to be totally deterministic
							// but we could anotate solutions with this info to
							// check if this is the case...
							for (Set<OWLEntity> s : locInfo.getSolutions()) {
								compSignature.addAll(s);
								lSignature.removeAll(s);
							}
						else {
							nonFragmentAxiomsStillNonLocal.add(axiom);
							if (compSignature.isEmpty())
								nondeterministicSolutions.add(locInfo
										.getSolutions());
						}
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

		if (compSignature.isEmpty()) {

			// System.out.println("no deterministic solutions in the initialisation phase");

			// It is extremely unlikely (is it?) that none of the axioms outside
			// the fragment can be localised in a deterministic way,
			// but if that is the case then maybe we should pick only a few of
			// them that are not "too nondeterministic" to get started and
			// guide the choices about the more nondeterministic ones
			compSignature = new ListProcessor().getMinimalCombination(
					nondeterministicSolutions, lSignature.size());

			lSignatureModule.removeAll(nonFragmentAxiomsStillNonLocal);
		} else {
			// System.out.println("deterministic solutions in the initialisation phase");
		}

		// System.out.println("compSignature of size " + compSignature.size());

		// //and now remove also all the symbols in the bot module for the
		// current complementary signature
		// for (OWLAxiom a : moduleExtractor.extract(compSignature)){
		// compSignature.addAll(a.getClassesInSignature());
		// }
		//
		// System.out.println("compSignature of size " + compSignature.size() +
		// " after adding to it the entities in the compModule");

		lSignature.removeAll(compSignature);
	}

	protected void reduceLsignature() {

		LinkedList<List<Set<OWLEntity>>> nondeterministicSolutions = new LinkedList<List<Set<OWLEntity>>>();
		boolean someDeterministicSolsFound = false;

		Set<OWLAxiom> newLocalNonFragmentAxiomsDet = new HashSet<OWLAxiom>();
		Set<OWLAxiom> newLocalNonFragmentAxiomsNondet = new HashSet<OWLAxiom>();
		for (OWLAxiom axiom : nonFragmentAxiomsStillNonLocal) {
			LocalityInfo locInfo = locChecker.isLocalAxiom(axiom, lSignature,
					globalEntities);
			if (!locInfo.is())
				if (locInfo.canMake()) {
					if (locInfo.getSolutions().size() == 1) {
						for (Set<OWLEntity> s : locInfo.getSolutions()) {
							compSignature.addAll(s);
							lSignature.removeAll(s);
						}
						newLocalNonFragmentAxiomsDet.add(axiom);
						someDeterministicSolsFound = true;
					} else {
						if (!someDeterministicSolsFound)
							nondeterministicSolutions.add(locInfo
									.getSolutions());
						newLocalNonFragmentAxiomsNondet.add(axiom);
					}

				} else {
					System.out.println("empty lSignature due to axiom "
							+ axiom.toString());
					lSignature = new HashSet<OWLEntity>();
					compSignature = ontology.getSignature();
					lSignatureModule = new HashSet<OWLAxiom>();
					return;
				}
		}
		nonFragmentAxiomsStillNonLocal.removeAll(newLocalNonFragmentAxiomsDet);

		Set<OWLAxiom> newLocalFragmentAxiomsDet = new HashSet<OWLAxiom>();
		Set<OWLAxiom> newLocalFragmentAxiomsNondet = new HashSet<OWLAxiom>();
		for (OWLAxiom axiom : lSignatureModule) {
			// LocalityInfo locInfo = localityChecker.isLocalAxiom(axiom,
			// lSignature);
			if (!lSignature.containsAll(axiom.getSignature())) {
				LocalityInfo locInfo = locChecker.isLocalAxiom(axiom,
						lSignature, globalEntities);
				if (!locInfo.is())
					if (locInfo.canMake()) {

						if (locInfo.getSolutions().size() == 1) {
							for (Set<OWLEntity> s : locInfo.getSolutions()) {
								compSignature.addAll(s);
								lSignature.removeAll(s);
							}
							newLocalFragmentAxiomsDet.add(axiom);
							someDeterministicSolsFound = true;
						} else {
							if (!someDeterministicSolsFound)
								nondeterministicSolutions.add(locInfo
										.getSolutions());
							newLocalFragmentAxiomsNondet.add(axiom);
						}

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
		lSignatureModule.removeAll(newLocalFragmentAxiomsDet);

		if (!someDeterministicSolsFound) {

			// System.out.println("no deterministic solutions in this reduction phase");

			Set<OWLEntity> notInLsignature = new ListProcessor()
					.getMinimalCombination(nondeterministicSolutions,
							lSignature.size());
			compSignature.addAll(notInLsignature);
			lSignatureModule.removeAll(newLocalFragmentAxiomsNondet);
			lSignatureModule.removeAll(newLocalNonFragmentAxiomsNondet);
		} else {
			// System.out.println("deterministic solutions in this reduction phase");
		}

		// System.out.println("compSignature of size " + compSignature.size());

		// //and now remove also all the symbols in the bot module for the
		// currebt complementary signature
		// for (OWLAxiom a : moduleExtractor.extract(compSignature)){
		// compSignature.addAll(a.getClassesInSignature());
		// }
		//
		// System.out.println("compSignature of size " + compSignature.size() +
		// " after adding to it the entities in the compModule");

		lSignature.removeAll(compSignature);

	}

}
