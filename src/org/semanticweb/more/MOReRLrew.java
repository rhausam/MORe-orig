package org.semanticweb.more;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.HermiT.graph.Graph;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.Individual;
import org.semanticweb.HermiT.tableau.ExtensionManager;
import org.semanticweb.HermiT.tableau.ExtensionTable;
import org.semanticweb.HermiT.tableau.ExtensionTable.Retrieval;
import org.semanticweb.HermiT.tableau.ReasoningTaskDescription;
import org.semanticweb.HermiT.tableau.Tableau;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.more.RLrewriting.RLrewOntology;
import org.semanticweb.more.hermit.HermiTforMORe;
import org.semanticweb.more.io.LogOutput;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLDocumentFormatImpl;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.reasoner.AxiomNotInProfileException;
import org.semanticweb.owlapi.reasoner.ClassExpressionNotInProfileException;
import org.semanticweb.owlapi.reasoner.FreshEntitiesException;
import org.semanticweb.owlapi.reasoner.InconsistentOntologyException;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.ReasonerInterruptedException;
import org.semanticweb.owlapi.reasoner.TimeOutException;
import org.semanticweb.owlapi.reasoner.UnsupportedEntailmentTypeException;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNode;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNodeSet;
import org.semanticweb.owlapi.util.InferredAxiomGenerator;
import org.semanticweb.owlapi.util.InferredEquivalentClassAxiomGenerator;
import org.semanticweb.owlapi.util.InferredOntologyGenerator;
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

//import uk.ac.manchester.syntactic_locality.ModuleExtractor;

/**
 * 
 * @author Ana Armas
 *
 */
public class MOReRLrew extends MOReReasoner {

	// protected Set<OWLEntity> lSymbolsInCompModule;

	protected OWLReasoner mergedReasoner;
	protected final String iri_merged_class_ontology = "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/merged_class_ontology.owl";
	protected OWLOntology merged_class_ontology;

	protected final int classifiedWithRLrew = 3;

	protected long timeForLsignature;
	protected long timeForELK;
	protected long timeForMergedOnto;
	protected long timeForELKMerged;
	protected long timeForRLrewriting;
	protected long timeForMaterialization;
	protected long timeForHermiT;

	public MOReRLrew(OWLOntology ontlgy) {// throws OWLOntologyCreationException
											// {
		this(ontlgy, true, false, null);
	}

	// Called from factory
	public MOReRLrew(OWLOntology ontlgy, boolean isBuffered,
			OWLReasonerConfiguration config) {// throws
												// OWLOntologyCreationException
												// {
		this(ontlgy, isBuffered, false, config);
	}

	public MOReRLrew(OWLOntology ontlgy, boolean isBuffered,
			boolean normalizeAxioms, OWLReasonerConfiguration config) {// throws
																		// OWLOntologyCreationException
																		// {
		super(ontlgy, isBuffered, normalizeAxioms, config);
		// fix this so that it works with any computer
	}

	public void classifyClasses() {

		flushChangesIfRequired();

		if (classified == notYetClassified) {

			try {

				// Unload compmodule and lmodule ontologies
				unloadOntologyFragmentsFromManager();

				if (isMonitorUp) {
					configuration.getProgressMonitor().reasonerTaskStarted(
							"Classifying the ontology with MORe B Experimental "
									+ getReasonerVersionStr() + "...");
					configuration.getProgressMonitor().reasonerTaskBusy();
				}

				computeLowerBoundClassificationWithELK();
				// Step 1
				// if (isMonitorUp){
				// configuration.getProgressMonitor().reasonerTaskProgressChanged(1,
				// 8);
				// }

				findLsignature();

				// creates compmodule_onto
				extractComplementModuleOntology();

				// uses compmodule_onto for the rewritting
				Graph<AtomicConcept> upperBound = computeUpperBoundClassification();

				// updates compmodule_onto
				refineCompModule(upperBound);

				Graph<AtomicConcept> knownSubsumptions = getKnownSubsumptionsGraphForCompModule(); // a
																									// more
																									// efficient
																									// way
																									// of
																									// doing
																									// this?

				// classifies compmodule_onto
				checkRemainingSubsumtionsWithHermiT(upperBound,
						knownSubsumptions);

				// create new ontology with inferences and classifies with ELK
				mergeClassificationsAndReasonWithELK();

				classified = classifiedWithRLrew;

				// finalOutputMessage = finalOutputMessage + "\n elk took " +
				// timeForELK + ", RLrewriting took " + timeForRLrewriting +
				// "Materialization took " + timeForMaterialization +
				// " and HermiT took " + timeForHermiT;
			} finally {
				// Final step
				if (isMonitorUp) {
					configuration.getProgressMonitor().reasonerTaskStopped();
				}
			}
		}

		// we still need to add a last check for satisfiability??
		// not if we MODIFY THE RLREWRITING so that we also preserve
		// unsatisfiability

	}

	/**
	 * We also unload the merged ontlogy from classification
	 */
	protected void unloadOntologyFragmentsFromManager() {
		super.unloadOntologyFragmentsFromManager();

		if (mergedReasoner != null) {
			mergedReasoner.dispose();
		}

		if (manager.contains(IRI.create(iri_merged_class_ontology))) {
			manager.removeOntology(merged_class_ontology);
			merged_class_ontology = null;
		}

	}

	private void computeLowerBoundClassificationWithELK() {
		// Logger.getLogger("org.semanticweb.elk").setLevel(Level.ERROR);//this
		// is to make elk less chatty: only errors
		//Logger.getLogger("org.semanticweb.elk").setLevel(Level.OFF);// removed
																	// completely
		Logger.getLogger("org.semanticweb.elk").setLevel(Level.INFO);
		timeForELK = System.currentTimeMillis();
		lReasoner = new ElkReasonerFactory()
				.createNonBufferingReasoner(ontology);
		lReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
		timeForELK = System.currentTimeMillis() - timeForELK;
	}

	protected Graph<AtomicConcept> getKnownSubsumptionsGraphForCompModule() {

		Graph<AtomicConcept> hierarchyGraph = new Graph<AtomicConcept>();
		for (OWLClass c : compmodule_onto.getClassesInSignature()) {
			// if (e instanceof OWLClass){// &&
			// !e.toString().contains("PAL-CONSTRAINT")){//WHAT IS THIS
			// PAL-CONSTRAINT THAT APPEARS FROM NOWHERE??
			// OWLClass c = (OWLClass) e;
			AtomicConcept ac = AtomicConcept.create(c.getIRI().toString());
			for (OWLClass sup : lReasoner.getSuperClasses(c, true)
					.getFlattened())
				hierarchyGraph.addEdge(ac,
						AtomicConcept.create(sup.getIRI().toString()));
			for (OWLClass eq : lReasoner.getEquivalentClasses(c)) {
				hierarchyGraph.addEdge(ac,
						AtomicConcept.create(eq.getIRI().toString()));
				hierarchyGraph.addEdge(
						AtomicConcept.create(eq.getIRI().toString()), ac);
			}
		}
		return hierarchyGraph;
	}

	protected void checkRemainingSubsumtionsWithHermiT(
			Graph<AtomicConcept> upperBound,
			Graph<AtomicConcept> knownSubsumptions) {
		timeForHermiT = System.currentTimeMillis();
		owl2reasoner = new HermiTforMORe(compmodule_onto, upperBound,
				knownSubsumptions);
		// hermiT.classifyClasses();
		owl2reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
		timeForHermiT = System.currentTimeMillis() - timeForHermiT;
		LogOutput
				.print("HermiT took "
						+ timeForHermiT
						+ " milliseconds to complete the classification with the refined module");
	}

	/**
	 * This method gets the classification results from ELK and HemriT and
	 * merges them in a new ontology We will use this ontology to produce the
	 * outputs
	 */
	private void mergeClassificationsAndReasonWithELK() {
		//Logger.getLogger("org.semanticweb.elk").setLevel(Level.ERROR);// this is
																		// to
																		// make
																		// elk
																		// less
																		// chatty
		Logger.getLogger("org.semanticweb.elk").setLevel(Level.INFO);

		timeForMergedOnto = System.currentTimeMillis();
		AdaptedInferredOntologyGenerator generator;
		Set<OWLAxiom> mergedAxioms = new HashSet<OWLAxiom>();

		// Create merged ontology with inferences from hermit and elk
		generator = new AdaptedInferredOntologyGenerator(owl2reasoner);
		generator.fillInferredAxioms(mergedAxioms); // adds axioms to given set
		generator = new AdaptedInferredOntologyGenerator(lReasoner);
		generator.fillInferredAxioms(mergedAxioms);// adds axioms to given set

		try {
			merged_class_ontology = manager.createOntology(mergedAxioms,
					IRI.create(iri_merged_class_ontology));
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}

		// TODO Remove reasoners??
		mergedAxioms.clear();

		timeForMergedOnto = System.currentTimeMillis() - timeForMergedOnto;
		LogOutput.print("Time creating merged ontology " + timeForMergedOnto
				+ " milliseconds. Axioms: "
				+ merged_class_ontology.getAxiomCount() + ". Entities: "
				+ merged_class_ontology.getSignature().size());
		// end creating merged ontology

		// Reason only classification ontology
		timeForELKMerged = System.currentTimeMillis();
		mergedReasoner = new ElkReasonerFactory()
				.createNonBufferingReasoner(ontology);
		mergedReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
		timeForELKMerged = System.currentTimeMillis() - timeForELKMerged;
		LogOutput
				.print("ELK took "
						+ timeForELKMerged
						+ " milliseconds to complete the classification of the merged ontology");
	}

	protected void extractComplementModuleOntology() {

		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
				manager, ontology, ModuleType.BOT);
		// ModuleExtractor botModExtractorErnesto =
		// new ModuleExtractor(ontology, false, false);

		compSignature = new HashSet<OWLEntity>(ontology.getSignature());
		compSignature.removeAll(lSignature);

		try {
			// It is a global variable so that we can remove it form manager
			compmodule_onto = manager.createOntology(
					botModExtractor.extract(compSignature),
					IRI.create(iri_compmodule_ontology));
			// compModuleErnesto = manager.createOntology(
			// botModExtractorErnesto.extractModuleAxiomsForGroupSignature(compSignature),
			// IRI.create(moduleErnestoIRI));

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}

		// finalOutputMessage = finalOutputMessage +
		// "The complementary module contains " + compModule.getAxiomCount() +
		// " axioms and " +
		// compModule.getSignature().size() + " symbols";

		// LogOutput.print(finalOutputMessage);

		LogOutput.print("The complementary module contains "
				+ compmodule_onto.getAxiomCount() + " axioms");
		// LogOutput.print("and " + compModule.getSignature().size() +
		// " symbols");
		// LogOutput.print("The complementary module by Ernesto contains " +
		// compModuleErnesto.getAxiomCount() + " axioms");
		// LogOutput.print("and " + compModuleErnesto.getSignature().size() +
		// " symbols");

		// LogOutput.print("now we return from the metod that extracts the module");

	}

	protected Graph<AtomicConcept> computeUpperBoundClassification() {
		return computeUpperBoundClassification(compmodule_onto);
	}

	protected Graph<AtomicConcept> computeUpperBoundClassification(
			OWLOntology compmodule) {

		// There is quite likely we get an error

		Graph<AtomicConcept> candidateSubsumers = new Graph<AtomicConcept>();

		try {

			OWLDataFactory factory = new OWLDataFactoryImpl();
			// Set<OWLNamedIndividual> individuals = new
			// HashSet<OWLNamedIndividual>();
			Set<OWLAxiom> newABoxAxioms = new HashSet<OWLAxiom>();
			Map<Individual, AtomicConcept> conceptsForIndividuals = new HashMap<Individual, AtomicConcept>();
			Map<Individual, org.semanticweb.HermiT.tableau.Node> nodesForIndividuals = new HashMap<Individual, org.semanticweb.HermiT.tableau.Node>();
			// Map<AtomicConcept,OWLClass> conceptsForClasses = new
			// HashMap<AtomicConcept, OWLClass>();

			// Introduce an ABox assertion for each concept outside the
			// Lsignature
			for (OWLEntity e : compSignature)
				if (e instanceof OWLClass) {
					String[] s;
					if (e.toString().contains("#"))
						s = e.toString().split("#");
					else
						s = e.toString().split("/");
					for (String subSt : s)
						if (subSt.contains(">")) {
							String owlIndName = new String(e
									.toString()
									.replace("<", "")
									.replace(subSt,
											"ind" + subSt.replaceAll(">", "")));
							OWLNamedIndividual owlInd = factory
									.getOWLNamedIndividual(IRI
											.create(owlIndName));
							// individuals.add(owlInd);
							OWLAxiom ax = factory.getOWLClassAssertionAxiom(
									(OWLClass) e, owlInd);
							newABoxAxioms.add(ax);

							Individual ind = Individual.create(owlInd.getIRI()
									.toString());
							AtomicConcept ac = AtomicConcept.create(e.getIRI()
									.toString());
							conceptsForIndividuals.put(ind, ac);
							nodesForIndividuals.put(ind, null);
							// conceptsForClasses.put(ac, (OWLClass) e);
						}
				}

			// then rewrite the resulting ontology into owl rl

			timeForRLrewriting = System.currentTimeMillis();
			RLrewOntology rlOntology = new RLrewOntology(manager, compmodule,
					true);
			rlOntology.transform();
			// Output ontology is removed from the manager at the end
			OWLOntology rewrittenOntology = rlOntology.getOutputOntology();
			rlOntology.clearIntermediateOntologies();
			timeForRLrewriting = System.currentTimeMillis()
					- timeForRLrewriting;

			// LogOutput.print("RLrewritten ontology  has " +
			// rewrittenOntology.getAxiomCount() + " axioms");
			// LogOutput.print("individuals resulting from Skolemisation in RLrewriting "
			// + rewrittenOntology.getIndividualsInSignature().size());

			manager.addAxioms(rewrittenOntology, newABoxAxioms);

			// LogOutput.print("individuals introduced for candidate subsumptions retrieval "
			// + newABoxAxioms.size());

			// now we have HermiT realize the ontology
			timeForMaterialization = System.currentTimeMillis();
			Configuration config = new Configuration();
			Reasoner hermiT = new Reasoner(config, rewrittenOntology);

			Tableau tableau = hermiT.getTableau();

			// LogOutput.print(finalOutputMessage);

			// LogOutput.print("hermit is materialising");
			if (tableau.isSatisfiable(true, false, new HashSet<Atom>(),
					new HashSet<Atom>(), new HashSet<Atom>(),
					new HashSet<Atom>(), nodesForIndividuals,
					ReasoningTaskDescription.isABoxSatisfiable())) {

				timeForMaterialization = System.currentTimeMillis()
						- timeForMaterialization;
				// LogOutput.print("hermit finished materialising in " +
				// timeForMaterialization + "ms");

				long tRetrieval = System.currentTimeMillis();
				ExtensionManager em = tableau.getExtensionManager();
				ExtensionTable bet = em.getBinaryExtensionTable();
				Retrieval ret = bet.createRetrieval(
						new boolean[] { false, true },
						ExtensionTable.View.EXTENSION_THIS);
				int counter = 0;
				for (Individual i : nodesForIndividuals.keySet()) {
					counter++;
					ret.getBindingsBuffer()[1] = nodesForIndividuals.get(i)
							.getCanonicalNode();
					ret.open();
					while (!ret.afterLast()) {
						Object co = ret.getTupleBuffer()[0];
						if ((co instanceof AtomicConcept && !co.toString()
								.contains("internal"))
								&& !co.toString().contains("#TOP>"))
							candidateSubsumers.addEdge(
									conceptsForIndividuals.get(i),
									(AtomicConcept) co);
						ret.next();
					}
				}
				tRetrieval = System.currentTimeMillis() - tRetrieval;
				// LogOutput.print("candidate subsumers retrieved in " +
				// tRetrieval + "ms");
			}

			// Remove rewritten ontology from manager:
			manager.removeOntology(rewrittenOntology);
		} catch (Exception e) {
			LogOutput.print("Error when rewriting the ontology");
			// throw new ReasonerInterruptedException();
		}

		return candidateSubsumers;
	}

	protected void refineCompModule(Graph<AtomicConcept> upperBoundGraph) {
		Set<OWLClass> classesFullyClassifiedByELK = new HashSet<OWLClass>();
		for (OWLEntity e : compSignature) {
			if (e instanceof OWLClass) {
				AtomicConcept ac = AtomicConcept.create(e.getIRI().toString());
				Set<AtomicConcept> lowerBound = new HashSet<AtomicConcept>();
				for (OWLClass c : lReasoner
						.getSuperClasses((OWLClass) e, false).getFlattened())
					lowerBound.add(AtomicConcept.create(c.getIRI().toString()));
				Set<AtomicConcept> upperBound = upperBoundGraph
						.getReachableSuccessors(ac);
				upperBound.remove(ac);
				if (lowerBound.containsAll(upperBound))
					classesFullyClassifiedByELK.add((OWLClass) e);

			}
		}

		// Included in both lower and upper bound classification
		compSignature.removeAll(classesFullyClassifiedByELK);

		lSignature.addAll(classesFullyClassifiedByELK);

		LogOutput.print("initial complementary module has "
				+ compmodule_onto.getAxiomCount() + " axioms");
		long tRefining = System.currentTimeMillis();

		// we remove previous complementary module from manager
		manager.removeOntology(compmodule_onto);
		compmodule_onto = null;

		try {
			SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
					manager, ontology, ModuleType.BOT);
			compmodule_onto = manager.createOntology(
					botModExtractor.extract(compSignature),
					IRI.create(iri_compmodule_ontology));

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}

		tRefining = System.currentTimeMillis() - tRefining;
		// LogOutput.print("refining took " + tRefining + "ms");
		LogOutput.print("extended lSignature has " + lSignature.size()
				+ "symbols");
		LogOutput.print("\n after refining compModule has "
				+ compmodule_onto.getAxiomCount() + " axioms");

		// for (OWLAxiom ax : ontology.getAxioms())
		// if (!compModule.getAxioms().contains(ax))
		// LogOutput.print(ax.toString() + " es local local");

	}

	// methods inherited from the OWLReasoner interface

	@Override
	public Node<OWLClass> getEquivalentClasses(OWLClassExpression arg0)
			throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {

		classifyClasses();

		return mergedReasoner.getEquivalentClasses(arg0);

		// /////////////REVISE THIS
		/*
		 * Set<OWLClass> equivClasses = null; if (arg0 instanceof OWLClass){
		 * OWLClass owlNothing = new OWLDataFactoryImpl().getOWLNothing(); if
		 * (lSignature.contains(arg0)){ equivClasses = new
		 * HashSet<OWLClass>(lReasoner.getEquivalentClasses((OWLClass)
		 * arg0).getEntities()); if (equivClasses.contains(owlNothing))
		 * equivClasses.addAll(hermiT.getUnsatisfiableClasses().getEntities());
		 * } else{ equivClasses = new
		 * HashSet<OWLClass>(hermiT.getEquivalentClasses((OWLClass)
		 * arg0).getEntities()); if (equivClasses.contains(owlNothing))
		 * equivClasses
		 * .addAll(lReasoner.getUnsatisfiableClasses().getEntities()); } return
		 * new OWLClassNode(equivClasses); } else{
		 * LogOutput.print("not supported"); return null; }
		 */
	}

	@Override
	public NodeSet<OWLClass> getSubClasses(OWLClassExpression arg0, boolean arg1)
			throws ReasonerInterruptedException, TimeOutException,
			FreshEntitiesException, InconsistentOntologyException,
			ClassExpressionNotInProfileException {

		classifyClasses();

		return mergedReasoner.getSubClasses(arg0, arg1);

		/*
		 * OWLClassNodeSet subClasses = null; if (lSignature.contains(arg0))
		 * subClasses = new OWLClassNodeSet(lReasoner.getSubClasses(arg0,
		 * arg1).getNodes()); if (compSignature.contains(arg0)) if (subClasses
		 * == null) subClasses = new OWLClassNodeSet(hermiT.getSubClasses(arg0,
		 * arg1).getNodes()); else
		 * subClasses.addAllNodes(hermiT.getSubClasses(arg0, arg1).getNodes());
		 * return subClasses;
		 */
	}

	@Override
	public NodeSet<OWLClass> getSuperClasses(OWLClassExpression arg0,
			boolean arg1) throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		classifyClasses();

		return mergedReasoner.getSuperClasses(arg0, arg1);

		/*
		 * if (lSignature.contains(arg0)) return lReasoner.getSuperClasses(arg0,
		 * arg1); else return hermiT.getSuperClasses(arg0, arg1);
		 */
	}

	@Override
	public Node<OWLClass> getUnsatisfiableClasses()
			throws ReasonerInterruptedException, TimeOutException,
			InconsistentOntologyException {
		classifyClasses();

		return mergedReasoner.getUnsatisfiableClasses();

		/*
		 * Node<OWLClass> unsatClasses = null; unsatClasses =
		 * lReasoner.getUnsatisfiableClasses();
		 * 
		 * // LogOutput.print(unsatClasses.getSize()); //
		 * LogOutput.print(hermiT.getUnsatisfiableClasses().getSize());
		 * 
		 * unsatClasses.getEntities().addAll(hermiT.getUnsatisfiableClasses().
		 * getEntities());
		 * 
		 * // LogOutput.print(unsatClasses.getSize());
		 * 
		 * return unsatClasses;
		 */
	}

	@Override
	public void interrupt() {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isConsistent() throws ReasonerInterruptedException,
			TimeOutException {
		classifyClasses();
		// return mergedReasoner.isConsistent(); //which is giving a more
		// complete answer??
		return owl2reasoner.isConsistent();
	}

	/*
	 * @Override public boolean isEntailed(OWLAxiom arg0) throws
	 * ReasonerInterruptedException, UnsupportedEntailmentTypeException,
	 * TimeOutException, AxiomNotInProfileException, FreshEntitiesException,
	 * InconsistentOntologyException { // TODO Auto-generated method stub return
	 * false; }
	 * 
	 * @Override public boolean isEntailed(Set<? extends OWLAxiom> arg0) throws
	 * ReasonerInterruptedException, UnsupportedEntailmentTypeException,
	 * TimeOutException, AxiomNotInProfileException, FreshEntitiesException,
	 * InconsistentOntologyException { // TODO Auto-generated method stub return
	 * false; }
	 */

	// TODO
	public void printHierarchy(File outputFile) throws FileNotFoundException,
			OWLOntologyCreationException, OWLOntologyStorageException {
		classifyClasses();
		// To generate an inferred ontology we use implementations of inferred
		// axiom generators
		List<InferredAxiomGenerator<? extends OWLAxiom>> gens = new ArrayList<InferredAxiomGenerator<? extends OWLAxiom>>();
		gens.add(new InferredSubClassAxiomGenerator());
		gens.add(new InferredEquivalentClassAxiomGenerator());

		// Put the inferred axioms into a fresh empty ontology.
		OWLOntologyManager man = OWLManager.createOWLOntologyManager();
		OWLOntology infOnt = man.createOntology();

		InferredOntologyGenerator iog = null;

		iog = new InferredOntologyGenerator(owl2reasoner, gens);
		iog.fillOntology(man.getOWLDataFactory(), infOnt);

		// Save the inferred ontology.
		OWLDocumentFormatImpl format = new FunctionalSyntaxDocumentFormat();
		man.saveOntology(infOnt, format, IRI.create(outputFile.toURI()));

	}

	public static void main(String[] argv) throws FileNotFoundException,
			OWLOntologyStorageException {

		String str_iri = "file:/usr/local/data/DataUMLS/fly_anatomy_XP.owl.zip";

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		try {

			MOReRLrew MORe = new MOReRLrew(manager.loadOntology(IRI
					.create(str_iri)));

			// MOReReasoner MORe = new
			// MOReReasoner(manager.loadOntology(IRI.create(str_iri)));

			long tClassification = System.currentTimeMillis();
			MORe.precomputeInferences(InferenceType.CLASS_HIERARCHY);
			tClassification = System.currentTimeMillis() - tClassification;
			System.out.print("Time classification: " + tClassification);
			MORe.dispose();

		} catch (Exception e) {
			e.printStackTrace();
		}

	}

}
