package org.semanticweb.more;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.more.io.LogOutput;

import org.apache.log4j.Logger;
import org.apache.log4j.Level;

import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.more.lsignature.ImprovedLsignatureExtractor;
import org.semanticweb.more.lsignature.LessGreedyImprovedLsignatureExtractor;
import org.semanticweb.more.lsignature.LsignatureExtractor;
import org.semanticweb.more.visitors.ELAxiomVisitor;
import org.semanticweb.more.visitors.ELKAxiomVisitor;
import org.semanticweb.more.visitors.NormalizeOWLAxiomVisitor;
import org.semanticweb.more.visitors.OWLFragmentVisitor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.RemoveAxiom;
import org.semanticweb.owlapi.model.OWLOntologyChangeListener;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLDocumentFormatImpl;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.AddOntologyAnnotation;
import org.semanticweb.owlapi.model.RemoveOntologyAnnotation;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.AxiomNotInProfileException;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.ClassExpressionNotInProfileException;
import org.semanticweb.owlapi.reasoner.FreshEntitiesException;
import org.semanticweb.owlapi.reasoner.FreshEntityPolicy;
import org.semanticweb.owlapi.reasoner.InconsistentOntologyException;
import org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy;
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
import org.semanticweb.owlapi.reasoner.impl.OWLDataPropertyNode;
import org.semanticweb.owlapi.reasoner.impl.OWLDataPropertyNodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLNamedIndividualNode;
import org.semanticweb.owlapi.reasoner.impl.OWLNamedIndividualNodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLObjectPropertyNode;
import org.semanticweb.owlapi.reasoner.impl.OWLObjectPropertyNodeSet;
import org.semanticweb.owlapi.util.InferredAxiomGenerator;
import org.semanticweb.owlapi.util.InferredEquivalentClassAxiomGenerator;
import org.semanticweb.owlapi.util.InferredOntologyGenerator;
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator;
import org.semanticweb.owlapi.util.Version;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

public class MOReReasoner implements OWLReasoner {

	/** Original ontology **/
	protected final OWLOntology root_ontology;

	/** Working ontology **/
	protected OWLOntology ontology;
	protected final String iri_str_working_ontology = "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/working_copy.owl";
	protected final String iri_compmodule_ontology = "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/compmodule_copy.owl";
	protected final String iri_lmodule_ontology = "http://www.cs.ox.ac.uk/isg/tools/MORe/ontologies/lmodule_copy.owl";

	/**
	 * We need to keep them to remove them from reasoner before reclassifying
	 * This can be avoided if incremental functionalities are implemented
	 **/
	protected OWLOntology lmodule_onto;
	protected OWLOntology compmodule_onto;

	/** Listener to track ontology changes (Very important for Protege plugin) **/
	protected final OntologyChangeListener root_ontologyChangeListener;

	/** Changes if incremental classification **/
	protected final List<OWLOntologyChange> pendingChanges_root_ontology;

	protected OWLOntologyManager manager;
	//
	protected OWLReasoner owl2reasoner;
	// protected Reasoner hermiT;
	protected OWLReasoner lReasoner;
	protected Set<OWLEntity> lSignature;
	protected Set<OWLAxiom> lModuleAxioms;
	protected Set<OWLEntity> compSignature;
	protected int classified;
	protected int compModuleSize = 0;// only for test checks, not necessary

	protected OWLReasonerConfiguration configuration;
	protected boolean isMonitorUp;

	protected boolean normalizeAxioms;
	protected boolean isBuffered;

	protected final int notYetClassified = 2;
	protected final int classifiedWithElk = 1;
	protected final int classifiedWithOWL2Reasoner = 0;

	protected int lFragment = ELKFRAGMENT;
	protected final static int ELKFRAGMENT = 1;
	protected final static int OWL2EL = 2;

	protected int OWL2REASONERID = OWL2ReasonerManager.HERMIT; // default

	protected static boolean interrupted = false;

	public MOReReasoner(OWLOntology ontlgy, boolean isBuffered,
			boolean normalizeAxioms, OWLReasonerConfiguration config) {

		// LogOutput.showOutpuLog(false);
		// interrupted = false;
		showAnyOutPut(false);
		// showOutPutLog(false);

		this.manager = OWLManager.createOWLOntologyManager();
		this.root_ontology = ontlgy;
		this.normalizeAxioms = normalizeAxioms;
		this.root_ontologyChangeListener = new OntologyChangeListener();
		root_ontology.getOWLOntologyManager().addOntologyChangeListener(
				root_ontologyChangeListener);
		this.pendingChanges_root_ontology = new ArrayList<OWLOntologyChange>();
		this.isBuffered = isBuffered;

		this.configuration = config;

		this.isMonitorUp = (configuration != null && configuration
				.getProgressMonitor() != null);

		LogOutput.print("Loading ontology in MORe: 1st time");
		loadOntology();

		printStatsAboutInputOntology();

	}

	public MOReReasoner(OWLOntology ontlgy, int fragment) {
		this(ontlgy, true, false, null);
		lFragment = fragment;
	}

	// Called from factory
	public MOReReasoner(OWLOntology ontlgy, boolean isBuffered,
			OWLReasonerConfiguration config) {
		this(ontlgy, isBuffered, false, config);
	}

	public MOReReasoner(OWLOntology ontlgy) {
		this(ontlgy, true, false, null);
	}

	public void setReasoner(int reasoner) {
		OWL2REASONERID = reasoner;
	}

	@Override
	public Version getReasonerVersion() {
		// TODO Update as ELK
		return new Version(0, 1, 7, 0);
		// return null;
	}

	public String getReasonerVersionStr() {
		// TODO Update as ELK
		return getReasonerVersion().getMajor() + "."
				+ getReasonerVersion().getMinor() + "."
				+ getReasonerVersion().getPatch();
		// return null;
	}

	public void showOutPutLog(boolean show) {
		LogOutput.showOutpuLog(show);
		// LogOutput.showOutpuLogAlways(show);
	}

	public void showAnyOutPut(boolean show) {
		LogOutput.showOutpuLog(show);
		LogOutput.showOutpuLogAlways(show);
	}

	protected void loadOntology() {

		// clear status
		// System.out.print("Clearing before loading.");
		clearStatus();

		try {
			if (normalizeAxioms)
				processInputOntology();
			else
				filterOntology();
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}

		// include lost signature
		includeLostSignature();

	}

	/**
	 * If ontology is reloaded then we should clear current status. e.g. unload
	 * ontology, reasoner, structures, etc... If incremental reasoning then the
	 * ontology may not be reloaded.
	 */
	protected void clearStatus() {

		this.classified = notYetClassified;

		this.pendingChanges_root_ontology.clear();

		// Unload working copy of the ontology
		if (manager.contains(IRI.create(iri_str_working_ontology))) {
			manager.removeOntology(ontology);
			this.ontology = null;
		}

		// Unload hermit and lreasoner ontologies
		unloadOntologyFragmentsFromManager();

		if (this.lSignature != null) {
			this.lSignature.clear();
		}
		if (this.lModuleAxioms != null) {
			this.lModuleAxioms.clear();
		}
		if (this.compSignature != null) {
			this.compSignature.clear();
		}

		// this.owl2reasoner = null;
		// this.lReasoner = null;

	}

	/**
	 * Unload from manager the subontologies given to hermit and lreasoner
	 * Dispose reasoners as well
	 */
	protected void unloadOntologyFragmentsFromManager() {

		// Dispose them if not null
		disposeUsedReasoners();

		if (manager.contains(IRI.create(iri_compmodule_ontology))) {
			manager.removeOntology(compmodule_onto);
			compmodule_onto = null;
		}
		if (manager.contains(IRI.create(iri_lmodule_ontology))) {
			manager.removeOntology(lmodule_onto);
			lmodule_onto = null;
		}
	}

	/**
	 * When filtering ontology some signature entities may be lost if they are
	 * not referenced in any Tbox or RBox axiom
	 */
	protected void includeLostSignature() {
		// Lost entities which were not appearing neither in RBox nor Tbox
		// axioms
		Set<OWLClass> signatureLost = new HashSet<OWLClass>();
		signatureLost.addAll(root_ontology.getClassesInSignature(true));
		signatureLost.removeAll(ontology.getClassesInSignature(true));

		Set<OWLAxiom> newSubTopAxioms = new HashSet<OWLAxiom>();

		for (OWLClass cls : signatureLost) {

			newSubTopAxioms.add(manager.getOWLDataFactory()
					.getOWLSubClassOfAxiom(cls,
							manager.getOWLDataFactory().getOWLThing()));

			newSubTopAxioms.add(manager.getOWLDataFactory()
					.getOWLDeclarationAxiom(cls));

		}

		// LogOutput.print("Ontology axioms: " + ontology.getAxiomCount());
		LogOutput.print("Adding lost signature to ontology: "
				+ newSubTopAxioms.size() + " axioms");
		manager.addAxioms(ontology, newSubTopAxioms);
		// LogOutput.print("Ontology axioms 2: " + ontology.getAxiomCount());

		signatureLost.clear();
		newSubTopAxioms.clear();
	}

	public Set<OWLEntity> getLsignature() {
		return lSignature;
	}

	public int getCompModuleSize() {
		return compModuleSize;
	}

	public void classifyClasses() {

		flushChangesIfRequired();

		if (classified == notYetClassified) {

			try {
				// Unload hermit and lreasoner ontologies and dispose reasoners
				// If incremental reasoning this may not be necessary
				unloadOntologyFragmentsFromManager();

				if (isMonitorUp) {

					String reasoner_name = OWL2ReasonerManager
							.getCurrentReasonerName(OWL2REASONERID);

					configuration.getProgressMonitor().reasonerTaskStarted(
							"Classifying the ontology with MORe A "
									+ reasoner_name + " "
									+ getReasonerVersionStr() + "...");
					configuration.getProgressMonitor().reasonerTaskBusy();
				}

				long tTotal = System.currentTimeMillis();
				findLsignature();

				// Step 1, if we know the concrete number of steps
				// if (isMonitorUp){
				// configuration.getProgressMonitor().reasonerTaskProgressChanged(1,
				// 3);
				// }

				computePartialClassificationWithHermiT();

				if (!lSignature.isEmpty()) {

					completeClassificationWithLreasoner();
				} else {
					classified = classifiedWithOWL2Reasoner;
					LogOutput
							.print("Because the computed Lsignature is empty, no other reasoner was used");
				}

				tTotal = System.currentTimeMillis() - tTotal;
				LogOutput.print("Whole classification took " + tTotal
						+ " milliseconds in total.");

				if (!isConsistent())
					LogOutput.print("The input ontology is inconsistent.");
			} finally {
				// Final step
				if (isMonitorUp) {
					configuration.getProgressMonitor().reasonerTaskStopped();
				}
			}
		}
	}

	protected void findLsignature() {
		// ImprovedLsignatureExtractor lSigExtractor = new
		// ImprovedLsignatureExtractor();
		LessGreedyImprovedLsignatureExtractor lSigExtractor = new LessGreedyImprovedLsignatureExtractor();

		lSignature = lSigExtractor.findLsignature(ontology,
				LsignatureExtractor.Fragment.ELK);
		compSignature = lSigExtractor.getCompSignature();
		lModuleAxioms = lSigExtractor.getLsignatureModule();

		// long tExt = System.currentTimeMillis();
		// lModuleAxioms = initialiseLsignature();
		// int currentSize = lSignature.size();
		// int previousSize = 0;
		// while (currentSize != previousSize) {
		// lModuleAxioms = reduceLsignature(lModuleAxioms);
		// previousSize = currentSize;
		// currentSize = lSignature.size();
		// }
		// tExt = System.currentTimeMillis() - tExt;
		// LogOutput.print("Lsignature extraction took " + tExt +
		// " milliseconds");// and "+ nIterations + " iterations");
		// LogOutput.print("Lsignature of size " + lSignature.size());
	}

	protected void computePartialClassificationWithHermiT() {
		try {
			Set<OWLAxiom> compModule = extractComplementModule();
			// We keep ontology given to HermiT in order to remove it from
			// mamnager when necessary
			// If incremental reasoning this can be done in a different way
			compmodule_onto = manager.createOntology(compModule,
					IRI.create(iri_compmodule_ontology));

			// /////////////
			// manager.setOntologyDocumentIRI(compmodule_onto,
			// IRI.create("file:/D:/Users/aarmas/Documents/Ontologies/compModule_CCOv2.01.owl"));
			// // manager.setOntologyFormat(normalisedCompModule, new
			// OWLFunctionalSyntaxOntologyFormat());
			// try {
			// manager.saveOntology(compmodule_onto);
			// } catch (OWLOntologyStorageException e) {
			// // TODO Auto-generated catch block
			// e.printStackTrace();
			// }
			// ////////////

			LogOutput.print(compmodule_onto.getAxiomCount()
					+ " axioms in comp module");

			// Setting OWL 2 Reasoner
			// ----------------------------
			owl2reasoner = OWL2ReasonerManager.createOWL2ReasonerInstance(
					compmodule_onto, OWL2REASONERID);
			String reasoner_name = OWL2ReasonerManager
					.getCurrentReasonerName(OWL2REASONERID);

			long towl2reasoner = System.currentTimeMillis();

			owl2reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
			// hermiT.classifyClasses();

			towl2reasoner = System.currentTimeMillis() - towl2reasoner;
			LogOutput.print(reasoner_name + " took " + towl2reasoner
					+ " milliseconds"); // to classify a module of size
										// " + compModule.size() + " axioms");

		} catch (OWLOntologyCreationException e) {
			System.err
					.println("Error classifying the DL module with HermiT (from MORe): "
							+ e.getMessage());
			e.printStackTrace();
		}
	}

	protected void completeClassificationWithLreasoner() {
		long tLreasoner = 0;
		// Logger.getLogger("org.semanticweb.elk").setLevel(Level.ERROR);//this
		// is to make elk less chatty: only errors
		//Logger.getLogger("org.semanticweb.elk").setLevel(Level.OFF);// removed
																	// completely
		Logger.getLogger("org.semanticweb.elk").setLevel(Level.INFO);

		boolean unifyAfter = false;
		Set<OWLAxiom> inferredAxioms = turnHierarchyIntoAxioms(owl2reasoner);
		// LogOutput.print(inferredAxioms.size());
		if (!compSignature.isEmpty()) {
			if (inferredAxioms.size() > 47000)// Biomodels had 49399 axioms
												// inferred by HermiT and it was
												// the only one which ever
												// caused problems with ELK
												// doing all at once
				unifyAfter = true;
			else
				lModuleAxioms.addAll(inferredAxioms);
		}

		try {
			// We keep ontology given to ELK in order to remove it from manager
			// when necessary
			// If incremental reasoning this can be done in a different way
			lmodule_onto = manager.createOntology(lModuleAxioms,
					IRI.create(iri_lmodule_ontology));
			lReasoner = new ElkReasonerFactory().createReasoner(lmodule_onto);
			tLreasoner = System.currentTimeMillis();
			lReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
			tLreasoner = System.currentTimeMillis() - tLreasoner;
			LogOutput.print("ELK took " + tLreasoner + "milliseconds");// to
																		// classify
																		// a
																		// module
																		// of
																		// size
																		// " + lModuleAxioms.size() + "
																		// axioms");

			if (unifyAfter) {
				long extraTime = System.currentTimeMillis();
				inferredAxioms.addAll(turnHierarchyIntoAxioms(lReasoner));
				lReasoner.dispose();
				lReasoner = new ElkReasonerFactory().createReasoner(manager
						.createOntology(inferredAxioms));
				lReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
				extraTime = System.currentTimeMillis() - extraTime;
				LogOutput.print(extraTime
						+ " extra milliseconds to unify both hierarchies");// to
																			// classify
																			// a
																			// module
																			// of
																			// size
																			// " + lModuleAxioms.size() + "
																			// axioms");
			}

			classified = classifiedWithElk;
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	protected void printStatsAboutInputOntology() {
		LogOutput.print("ontology has " + ontology.getAxiomCount()
				+ " TBox axioms, " + "\n of which " + nELKaxioms()
				+ " are ELK, " + "\n and signature of size "
				+ ontology.getSignature().size());
	}

	protected int nELaxioms() {
		int n = 0;
		ELAxiomVisitor visitor = new ELAxiomVisitor();
		for (OWLAxiom ax : ontology.getAxioms()) {
			ax.accept(visitor);
			if (visitor.isEL())
				n++;
		}
		return n;
	}

	protected int nELKaxioms() {
		int n = 0;
		ELKAxiomVisitor visitor = new ELKAxiomVisitor();
		n = ontology.getAxioms().stream().map((ax) -> {
			ax.accept(visitor);
			return ax;
		}).filter((_item) -> (visitor.isInFragment())).map((_item) -> 1)
				.reduce(n, Integer::sum);
		return n;
	}

	public boolean axiomInLfragment(OWLAxiom axiom, int fragment) {
		if (fragment == OWL2EL) {
			ELAxiomVisitor elAxiomVisitor = new ELAxiomVisitor();
			axiom.accept(elAxiomVisitor);
			return elAxiomVisitor.isEL();
		} else {
			ELKAxiomVisitor elkAxiomVisitor = new ELKAxiomVisitor();
			axiom.accept(elkAxiomVisitor);
			return elkAxiomVisitor.isInFragment();
		}
	}

	protected boolean isFullyEL(Set<OWLAxiom> axioms) {
		ELAxiomVisitor elVisitor = new ELAxiomVisitor();
		boolean booleanAcc = true;
		Iterator<OWLAxiom> iterator = axioms.iterator();
		OWLAxiom axiom;
		while (booleanAcc && iterator.hasNext()) {
			axiom = iterator.next();
			axiom.accept(elVisitor);
			booleanAcc = booleanAcc && elVisitor.isEL();
		}
		return booleanAcc;
	}

	// Not used as method. Use instead AdaptedInferredOntologyGenerator
	protected Set<OWLAxiom> turnHierarchyIntoAxioms(OWLReasoner r) {

		long t = System.currentTimeMillis();

		// from Ernesto
		List<InferredAxiomGenerator<? extends OWLAxiom>> gens = new ArrayList<>();
		gens.add(new InferredSubClassAxiomGenerator());
		gens.add(new InferredEquivalentClassAxiomGenerator());

		OWLOntology inferredOntology;
		try {
			inferredOntology = manager.createOntology();
			InferredOntologyGenerator iog = null;

			iog = new InferredOntologyGenerator(r, gens);
			iog.fillOntology(manager.getOWLDataFactory(), inferredOntology);

			t = System.currentTimeMillis() - t;
			LogOutput.print(t + "ms for the hierarchy rewriting");

			return inferredOntology.getAxioms();

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
			return null;
		}

	}

	protected Set<OWLAxiom> extractComplementModule() {
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
				manager, ontology, ModuleType.BOT);
		Set<OWLAxiom> compModule = botModExtractor.extract(compSignature);
		compModuleSize = compModule.size();
		return compModule;
	}

	// public static Set<OWLAxiom> extractComplementModule(
	// Set<OWLEntity> lSignature, OWLOntology ontology)
	// throws OWLOntologyCreationException {
	// OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	// SyntacticLocalityModuleExtractor botModExtractor = new
	// SyntacticLocalityModuleExtractor(
	// manager, ontology, ModuleType.BOT);
	// Set<OWLEntity> compSignature = ontology.getSignature();
	// compSignature.removeAll(lSignature);
	// Set<OWLAxiom> compModule = botModExtractor.extract(compSignature);
	// // LogOutput.print("complementary module has " + compModule.size() +
	// " axioms");
	// return compModule;
	// }

	public void processInputOntology() throws OWLOntologyCreationException {

		statisticsOriginalOntology(root_ontology);

		long timeNormalization = System.currentTimeMillis();

		// -- Normalisation ------------
		Set<OWLAxiom> normalizedAxioms = new HashSet<OWLAxiom>();
		NormalizeOWLAxiomVisitor normaliser = new NormalizeOWLAxiomVisitor(
				manager.getOWLDataFactory());

		OWLFragmentVisitor fragmentVisitor = new ELKAxiomVisitor();

		for (OWLAxiom ax : root_ontology.getTBoxAxioms(Imports.INCLUDED)) {

			ax.accept(fragmentVisitor);

			if (!fragmentVisitor.isInFragment()) {

				ax.accept(normaliser);

				normalizedAxioms.addAll(normaliser.getNormalizedAxioms()); // by
																			// default
																			// included
																			// the
																			// axioms
																			// itself

				if (!normaliser.wasAxiomProcessed()) { // Then we need to add it
					normalizedAxioms.add(ax);
				}

				normaliser.resetStructures();
			} else {
				normalizedAxioms.add(ax);
			}
		}
		// -- End Normalisation -----------------
		timeNormalization = System.currentTimeMillis() - timeNormalization;
		LogOutput.print("Normalisation took " + timeNormalization
				+ " milliseconds");

		ontology = manager.createOntology(IRI.create(iri_str_working_ontology)); // root_ontology.getOntologyID().getOntologyIRI()

		manager.addAxioms(ontology, normalizedAxioms);
		// manager.addAxioms(ontology, ontlgy.getTBoxAxioms(true));
		manager.addAxioms(ontology,
				root_ontology.getRBoxAxioms(Imports.INCLUDED));

		normalizedAxioms.clear();

		LogOutput.print("Signature normalized: "
				+ ontology.getSignature().size());

	}

	// No normalization
	public void statisticsOriginalOntology(OWLOntology ontlgy) {
		LogOutput.print("Signature original: " + ontlgy.getSignature().size());
		LogOutput.print("Original relevant ontology axioms: "
				+ (ontlgy.getTBoxAxioms(Imports.INCLUDED).size() + ontlgy
						.getRBoxAxioms(Imports.INCLUDED).size()));
		int n = 0;
		ELKAxiomVisitor visitor = new ELKAxiomVisitor();
		for (OWLAxiom ax : ontlgy.getTBoxAxioms(Imports.INCLUDED)) {
			ax.accept(visitor);
			if (visitor.isInFragment())
				n++;
		}
		for (OWLAxiom ax : ontlgy.getRBoxAxioms(Imports.INCLUDED)) {
			ax.accept(visitor);
			if (visitor.isInFragment())
				n++;
		}
		LogOutput.print("\tof which " + n + " are in the ELK fragment\n");
	}

	// ///////////////
	// public static Set<OWLAxiom> rewriteAxiomsForCB(Set<OWLAxiom> axioms){
	// Set<OWLAxiom> axiomsToBeRewritten = new HashSet<OWLAxiom>();
	// Set<OWLAxiom> rewrittenAxioms = new HashSet<OWLAxiom>();
	// OWLDataFactoryImpl factory = new OWLDataFactoryImpl();
	// for (OWLAxiom ax : axioms){
	// if (ax instanceof OWLDisjointClassesAxiom){
	// axiomsToBeRewritten.add(ax);
	// Set<OWLDisjointClassesAxiom> pairwise = ((OWLDisjointClassesAxiom)
	// ax).asPairwiseAxioms();
	// for (OWLDisjointClassesAxiom a : pairwise){
	// rewrittenAxioms.add(factory.getOWLSubClassOfAxiom(
	// factory.getOWLObjectIntersectionOf(a.getClassExpressions()),
	// factory.getOWLNothing()));
	// }
	// }
	// if (ax instanceof OWLObjectPropertyDomainAxiom){
	// axiomsToBeRewritten.add(ax);
	// rewrittenAxioms.add(factory.getOWLSubClassOfAxiom(
	// factory.getOWLObjectSomeValuesFrom(((OWLObjectPropertyDomainAxiom)
	// ax).getProperty(), factory.getOWLThing()),
	// ((OWLObjectPropertyDomainAxiom) ax).getDomain()));
	// }
	// if (ax instanceof OWLObjectPropertyRangeAxiom){
	// axiomsToBeRewritten.add(ax);
	// rewrittenAxioms.add(factory.getOWLSubClassOfAxiom(
	// factory.getOWLObjectSomeValuesFrom(
	// factory.getOWLObjectInverseOf(((OWLObjectPropertyRangeAxiom)
	// ax).getProperty()),
	// factory.getOWLThing()),
	// ((OWLObjectPropertyRangeAxiom) ax).getRange()));
	// }
	// if (ax instanceof OWLDataPropertyDomainAxiom){
	// axiomsToBeRewritten.add(ax);
	// rewrittenAxioms.add(factory.getOWLSubClassOfAxiom(
	// factory.getOWLDataSomeValuesFrom(((OWLDataPropertyDomainAxiom)
	// ax).getProperty(), factory.getTopDatatype()),
	// ((OWLDataPropertyDomainAxiom) ax).getDomain()));
	// }
	// if (ax instanceof OWLInverseFunctionalObjectPropertyAxiom){
	// axiomsToBeRewritten.add(ax);
	// rewrittenAxioms.add(factory.getOWLFunctionalObjectPropertyAxiom(
	// factory.getOWLObjectInverseOf(((OWLInverseFunctionalObjectPropertyAxiom)
	// ax).getProperty())));
	// }
	// if (ax instanceof OWLDeclarationAxiom){
	// axiomsToBeRewritten.add(ax);
	// }
	// }
	// axioms.removeAll(axiomsToBeRewritten);
	// axioms.addAll(rewrittenAxioms);
	// return axioms;
	// }
	// //////////////

	private void filterOntology() throws OWLOntologyCreationException {

		LogOutput.print("Signature original: "
				+ root_ontology.getSignature(Imports.INCLUDED).size());
		LogOutput.print("Class original: "
				+ root_ontology.getClassesInSignature(true).size());

		if (!root_ontology.getABoxAxioms(Imports.INCLUDED).isEmpty())
			LogOutput.print("This ontology contains assertional axioms");

		Set<OWLAxiom> filteredAxioms = new HashSet<>();
		filteredAxioms.addAll(root_ontology.getTBoxAxioms(Imports.INCLUDED));
		filteredAxioms.addAll(root_ontology.getRBoxAxioms(Imports.INCLUDED));
		ontology = manager.createOntology(filteredAxioms,
				IRI.create(iri_str_working_ontology));
	}

	private boolean checkSatisfiability(OWLClass c) {
		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
				manager, ontology, ModuleType.BOT);
		Set<OWLEntity> signature = new HashSet<>();
		signature.add(c);

		boolean isSat = true;

		try {
			MOReReasoner auxMORe = new MOReReasoner(
					botModExtractor.extractAsOntology(
							signature,
							IRI.create("http://org.semanticweb.more.orechallenge/moduleForSatisfiability")));

			isSat = !auxMORe.getUnsatisfiableClasses().contains(c);

			auxMORe.dispose();

		} catch (OWLOntologyCreationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return isSat;
	}

	/**
	 * Uses a module with OWL 2 Reasoner to check if a class expression "c" is
	 * satisfiable
	 */
	private boolean checkSatisfiability(OWLClassExpression c) {
		SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
				manager, ontology, ModuleType.BOT);
		Set<OWLEntity> signature = new HashSet<OWLEntity>();
		signature.addAll(c.getSignature());

		boolean isSat = true;

		try {
			OWLReasoner auxOWLReasoner = OWL2ReasonerManager
					.createOWL2ReasonerInstance(
							botModExtractor
									.extractAsOntology(
											signature,
											IRI.create("http://org.semanticweb.more.orechallenge/moduleForSatisfiability")),
							OWL2REASONERID);

			isSat = auxOWLReasoner.isSatisfiable(c);

			auxOWLReasoner.dispose();

		} catch (OWLOntologyCreationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return isSat;
	}

	// methods inherited from the OWLReasoner interface

	protected void disposeUsedReasoners() {
		// Can be empty if lsignature is empty
		if (lReasoner != null) {
			// lReasoner.interrupt();
			lReasoner.dispose();
		}

		if (owl2reasoner != null) {
			// owl2reasoner.interrupt();
			owl2reasoner.dispose();
		}
	}

	public void finalize() {
		dispose();
	}

	@Override
	public void dispose() {

		// remove ontology change listener
		root_ontology.getOWLOntologyManager().removeOntologyChangeListener(
				root_ontologyChangeListener);
		// disposeUsedReasoners and others

		// System.out.print("Clearing dispose.");
		clearStatus();

	}

	// Ontology change management methods

	protected class OntologyChangeListener implements OWLOntologyChangeListener {
		public void ontologiesChanged(List<? extends OWLOntologyChange> changes)
				throws OWLException {
			for (OWLOntologyChange change : changes) {
				if (!(change instanceof RemoveOntologyAnnotation || change instanceof AddOntologyAnnotation)) {
					pendingChanges_root_ontology.add(change);
					// classified = notYetClassified;
					// LogOutput.print("Registered change: " + change);
				}
			}
		}
	}

	protected void flushChangesIfRequired() {
		if (!isBufferingMode() && !pendingChanges_root_ontology.isEmpty())
			// if (!pendingChanges_root_ontology.isEmpty())
			flush();
	}

	@Override
	public void flush() {

		if (!pendingChanges_root_ontology.isEmpty()) {

			// TODO Incremental method (ernesto)
			// if MORe incremenal
			// do incremental classification
			// else
			LogOutput.print("Loading ontology in MORe: after flush");
			loadOntology();

			// We empty changes
			pendingChanges_root_ontology.clear();
		}
	}

	protected boolean isBufferingMode() {
		return isBuffered;
	}

	@Override
	public BufferingMode getBufferingMode() {
		if (isBufferingMode()) {
			return BufferingMode.BUFFERING;
		} else {
			return BufferingMode.NON_BUFFERING;
		}
	}

	@Override
	public Set<OWLAxiom> getPendingAxiomAdditions() {
		Set<OWLAxiom> added = new HashSet<OWLAxiom>();
		for (OWLOntologyChange change : pendingChanges_root_ontology) {
			if (change instanceof AddAxiom) {
				added.add(change.getAxiom());
			}
		}
		return added;
	}

	@Override
	public Set<OWLAxiom> getPendingAxiomRemovals() {
		Set<OWLAxiom> removed = new HashSet<OWLAxiom>();
		for (OWLOntologyChange change : pendingChanges_root_ontology) {
			if (change instanceof RemoveAxiom) {
				removed.add(change.getAxiom());
			}
		}
		return removed;
	}

	@Override
	public List<OWLOntologyChange> getPendingChanges() {
		return pendingChanges_root_ontology;
	}

	// END: Ontology change management methods

	@Override
	public Node<OWLClass> getBottomClassNode() {
		// LogOutput.printNotSupported("Not supported");
		// return null;
		classifyClasses();
		switch (classified) {
		case classifiedWithElk:
			return lReasoner.getBottomClassNode();
		case classifiedWithOWL2Reasoner:
			return owl2reasoner.getBottomClassNode();
		default:
			LogOutput
					.printAlways("Classification not computed yet: getBottomClassNode");
			// return null;
			return new OWLClassNode(manager.getOWLDataFactory().getOWLNothing());
		}
	}

	@Override
	public Node<OWLDataProperty> getBottomDataPropertyNode() {
		LogOutput.printNotSupported("Not supported: getBottomDataPropertyNode");
		// return null;
		// return new OWLDataPropertyNode();
		return new OWLDataPropertyNode(manager.getOWLDataFactory()
				.getOWLBottomDataProperty());
	}

	@Override
	public Node<OWLObjectPropertyExpression> getBottomObjectPropertyNode() {
		LogOutput
				.printNotSupported("Not supported: getBottomObjectPropertyNode");
		// return null;
		// return new OWLObjectPropertyNode();
		return new OWLObjectPropertyNode(manager.getOWLDataFactory()
				.getOWLBottomObjectProperty());
	}

	@Override
	public NodeSet<OWLClass> getDataPropertyDomains(OWLDataProperty arg0,
			boolean arg1) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException,
			TimeOutException {
		LogOutput.printNotSupported("Not supported: getDataPropertyDomains");
		// return null;
		return new OWLClassNodeSet();
	}

	@Override
	public Set<OWLLiteral> getDataPropertyValues(OWLNamedIndividual arg0,
			OWLDataProperty arg1) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException,
			TimeOutException {
		LogOutput.printNotSupported("Not supported: getDataPropertyValues");
		// return null;
		return new HashSet<OWLLiteral>();
	}

	@Override
	public NodeSet<OWLNamedIndividual> getDifferentIndividuals(
			OWLNamedIndividual arg0) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException,
			TimeOutException {
		LogOutput.printNotSupported("Not supported: getDifferentIndividuals");
		// return null;
		return new OWLNamedIndividualNodeSet();
	}

	@Override
	public NodeSet<OWLClass> getDisjointClasses(OWLClassExpression ce)
			throws ReasonerInterruptedException, TimeOutException,
			FreshEntitiesException, InconsistentOntologyException {
		LogOutput
				.printNotSupported("Not supported: getDisjointClasses. Returning explicit disjoint classes.");
		// return null;

		OWLClassNodeSet nodeSet = new OWLClassNodeSet();
		if (!ce.isAnonymous()) {
			for (OWLOntology ontology : getRootOntology().getImportsClosure()) {
				for (OWLDisjointClassesAxiom ax : ontology
						.getDisjointClassesAxioms(ce.asOWLClass())) {
					for (OWLClassExpression op : ax.getClassExpressions()) {
						if (!op.isAnonymous() && !op.equals(ce)) { // Op must be
																	// differnt
																	// to ce
							nodeSet.addNode(getEquivalentClasses(op));
						}
					}
				}
			}
		}
		return nodeSet;

	}

	@Override
	public NodeSet<OWLDataProperty> getDisjointDataProperties(
			OWLDataPropertyExpression arg0)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getDisjointDataProperties");
		// return null;
		return new OWLDataPropertyNodeSet();
	}

	@Override
	public NodeSet<OWLObjectPropertyExpression> getDisjointObjectProperties(
			OWLObjectPropertyExpression arg0)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput
				.printNotSupported("Not supported: getDisjointObjectProperties");
		// return null;
		return new OWLObjectPropertyNodeSet();
	}

	@Override
	public Node<OWLClass> getEquivalentClasses(OWLClassExpression arg0)
			throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		classifyClasses();
		switch (classified) {
		case classifiedWithElk:
			return lReasoner.getEquivalentClasses(arg0);
		case classifiedWithOWL2Reasoner:
			return owl2reasoner.getEquivalentClasses(arg0);
		default:
			LogOutput
					.printAlways("Classification not computed yet: getEquivalentClasses");
			// return null;
			return new OWLClassNode();
		}

		// if (lSignature.contains(arg0))
		// return elk.getEquivalentClasses(arg0);
		// else
		// return hermiT.getEquivalentClasses(arg0);
	}

	@Override
	public Node<OWLDataProperty> getEquivalentDataProperties(
			OWLDataProperty arg0) throws InconsistentOntologyException,
			FreshEntitiesException, ReasonerInterruptedException {
		LogOutput
				.printNotSupported("Not supported: getEquivalentDataProperties");
		// return null;
		return new OWLDataPropertyNode();
	}

	@Override
	public Node<OWLObjectPropertyExpression> getEquivalentObjectProperties(
			OWLObjectPropertyExpression arg0)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput
				.printNotSupported("Not supported: getEquivalentObjectProperties");
		// return null;
		return new OWLObjectPropertyNode();
	}

	@Override
	public FreshEntityPolicy getFreshEntityPolicy() {
		// /return null;
		// TODO copied from HermiT configuration
		return FreshEntityPolicy.ALLOW;
	}

	@Override
	public IndividualNodeSetPolicy getIndividualNodeSetPolicy() {
		// TODO
		// LogOutput.printNotSupported("Not supported: getIndividualNodeSetPolicy");
		// TODO copied from HermiT configuration
		return IndividualNodeSetPolicy.BY_NAME;
		// return null;
	}

	@Override
	public NodeSet<OWLNamedIndividual> getInstances(OWLClassExpression arg0,
			boolean arg1) throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		// TODO
		LogOutput.printNotSupported("Not supported: getInstances"); // Many
																	// messages???
		// for getInstances...
		return new OWLNamedIndividualNodeSet();
		// return null;
	}

	@Override
	public Node<OWLObjectPropertyExpression> getInverseObjectProperties(
			OWLObjectPropertyExpression arg0)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput
				.printNotSupported("Not supported: getInverseObjectProperties");
		// return null;
		return new OWLObjectPropertyNode();
	}

	@Override
	public NodeSet<OWLClass> getObjectPropertyDomains(
			OWLObjectPropertyExpression arg0, boolean arg1)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getObjectPropertyDomains");
		// return null;
		return new OWLClassNodeSet();
	}

	@Override
	public NodeSet<OWLClass> getObjectPropertyRanges(
			OWLObjectPropertyExpression arg0, boolean arg1)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getObjectPropertyRanges");
		// return null;
		return new OWLClassNodeSet();
	}

	@Override
	public NodeSet<OWLNamedIndividual> getObjectPropertyValues(
			OWLNamedIndividual arg0, OWLObjectPropertyExpression arg1)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getObjectPropertyValues");
		// return null;
		return new OWLNamedIndividualNodeSet();
	}

	@Override
	public Set<InferenceType> getPrecomputableInferenceTypes() {
		Set<InferenceType> sol = new HashSet<InferenceType>();
		sol.add(InferenceType.CLASS_HIERARCHY);
		return sol;
	}

	@Override
	public String getReasonerName() {
		return "MORe Reasoner";
	}

	@Override
	public OWLOntology getRootOntology() {
		return ontology;
	}

	@Override
	public Node<OWLNamedIndividual> getSameIndividuals(OWLNamedIndividual arg0)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getSameIndividuals");
		// return null;
		return new OWLNamedIndividualNode();
	}

	@Override
	public NodeSet<OWLClass> getSubClasses(OWLClassExpression arg0,
			boolean direct) throws ReasonerInterruptedException,
			TimeOutException, FreshEntitiesException,
			InconsistentOntologyException, ClassExpressionNotInProfileException {
		classifyClasses();
		switch (classified) {
		case classifiedWithElk:
			return lReasoner.getSubClasses(arg0, direct);
		case classifiedWithOWL2Reasoner:
			return owl2reasoner.getSubClasses(arg0, direct);
		default:
			LogOutput
					.printAlways("Classification not computed yet: getSubClasses");
			// return null;
			return new OWLClassNodeSet();
		}

		// if (lSignature.contains(arg0))
		// return elk.getSubClasses(arg0, arg1);
		// else
		// return hermiT.getSubClasses(arg0, arg1);
	}

	@Override
	public NodeSet<OWLDataProperty> getSubDataProperties(
			OWLDataProperty direct, boolean arg1)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getSubDataProperties");
		// return null;
		return new OWLDataPropertyNodeSet();
	}

	@Override
	public NodeSet<OWLObjectPropertyExpression> getSubObjectProperties(
			OWLObjectPropertyExpression arg0, boolean direct)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getSubObjectProperties");
		// return null;
		return new OWLObjectPropertyNodeSet();
	}

	@Override
	public NodeSet<OWLClass> getSuperClasses(OWLClassExpression arg0,
			boolean direct) throws InconsistentOntologyException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		classifyClasses();
		switch (classified) {
		case classifiedWithElk:
			return lReasoner.getSuperClasses(arg0, direct);
		case classifiedWithOWL2Reasoner:
			return owl2reasoner.getSuperClasses(arg0, direct);
		default:
			LogOutput
					.printAlways("Classification not computed yet: getSuperClasses");
			// return null;
			return new OWLClassNodeSet();
		}

		// if (lSignature.isEmpty())
		// return hermiT.getSuperClasses(arg0, arg1);
		// else
		// if (compSignature.isEmpty())
		// return elk.getSuperClasses(arg0, arg1);
		// else{
		// if (getUnsatisfiableClasses().getEntities().contains(arg0)){
		// Set<Node<OWLClass>> nodes = new HashSet<Node<OWLClass>>();
		// nodes.addAll(hermiT.getSuperClasses(new
		// OWLDataFactoryImpl().getOWLNothing(), arg1).getNodes());
		// nodes.addAll(elk.getSuperClasses(new
		// OWLDataFactoryImpl().getOWLNothing(), arg1).getNodes());
		// return new OWLClassNodeSet(nodes);
		// }
		// else{
		// if (lSignature.contains(arg0))
		// return elk.getSuperClasses(arg0, arg1);
		// else
		// return hermiT.getSuperClasses(arg0, arg1);
		// }
		// }
	}

	@Override
	public NodeSet<OWLDataProperty> getSuperDataProperties(
			OWLDataProperty arg0, boolean direct)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getSuperDataProperties");
		// return null;
		return new OWLDataPropertyNodeSet();
	}

	@Override
	public NodeSet<OWLObjectPropertyExpression> getSuperObjectProperties(
			OWLObjectPropertyExpression arg0, boolean direct)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getSuperObjectProperties");
		// return null;
		return new OWLObjectPropertyNodeSet();
	}

	@Override
	public long getTimeOut() {
		return 0;
	}

	@Override
	public Node<OWLClass> getTopClassNode() {
		// LogOutput.printNotSupported("Not supported");
		// return null;
		classifyClasses();
		switch (classified) {
		case classifiedWithElk:
			return lReasoner.getTopClassNode();
		case classifiedWithOWL2Reasoner:
			return owl2reasoner.getTopClassNode();
		default:
			LogOutput
					.printAlways("Classification not computed yet: getTopClassNode");
			// return null;
			return new OWLClassNode(manager.getOWLDataFactory().getOWLThing());
		}
	}

	@Override
	public Node<OWLDataProperty> getTopDataPropertyNode() {
		LogOutput.printNotSupported("Not supported: getTopDataPropertyNode");
		// return null;
		return new OWLDataPropertyNode(manager.getOWLDataFactory()
				.getOWLTopDataProperty());
	}

	@Override
	public Node<OWLObjectPropertyExpression> getTopObjectPropertyNode() {
		LogOutput.printNotSupported("Not supported: getTopObjectPropertyNode");
		// return null;
		return new OWLObjectPropertyNode(manager.getOWLDataFactory()
				.getOWLTopObjectProperty());
	}

	@Override
	public NodeSet<OWLClass> getTypes(OWLNamedIndividual arg0, boolean arg1)
			throws InconsistentOntologyException, FreshEntitiesException,
			ReasonerInterruptedException, TimeOutException {
		LogOutput.printNotSupported("Not supported: getTypes");
		// return null;
		return new OWLClassNodeSet();
	}

	@Override
	public Node<OWLClass> getUnsatisfiableClasses()
			throws ReasonerInterruptedException, TimeOutException,
			InconsistentOntologyException {
		classifyClasses();
		switch (classified) {
		case classifiedWithElk:
			return lReasoner.getUnsatisfiableClasses();
		case classifiedWithOWL2Reasoner:
			return owl2reasoner.getUnsatisfiableClasses();
		default:
			LogOutput
					.printAlways("Classification not computed yet: getUnsatisfiableClasses");
			// return null;
			return new OWLClassNode();
		}

		// if (lSignature.isEmpty())
		// return hermiT.getUnsatisfiableClasses();
		// else
		// if (compSignature.isEmpty())
		// return elk.getUnsatisfiableClasses();
		// else{
		// Set<OWLClass> unsatClasses =
		// elk.getUnsatisfiableClasses().getEntities();
		// unsatClasses.addAll(hermiT.getUnsatisfiableClasses().getEntities());
		// return new OWLClassNode(unsatClasses);
		// }
	}

	@Override
	public void interrupt() {
		try {

			// TODO Check if behaviour is expected

			LogOutput.print("Interrupting MORe reasoner");
			interrupted = true;

			if (owl2reasoner != null) {
				owl2reasoner.interrupt();
				LogOutput.print("Done interrupting HermiT");

			}

			if (lReasoner != null) {
				lReasoner.interrupt();
				LogOutput.print("Done interrupting ELK");
			}

		} catch (Exception e) {
			LogOutput.print("Error interrupting reasoners");
		}
	}

	@Override
	public boolean isConsistent() throws ReasonerInterruptedException,
			TimeOutException {
		classifyClasses();
		switch (classified) {
		case classifiedWithElk:
			return lReasoner.isConsistent();
		case classifiedWithOWL2Reasoner:
			return owl2reasoner.isConsistent();
			// LogOutput.printAlways("HermiT: " + hermiT); //TODO
		default:
			LogOutput
					.printAlways("Classification not computed yet: isConsistent");
			return true;
		}

		// if (lSignature.isEmpty())
		// return hermiT.isConsistent();
		// else
		// if (compSignature.isEmpty())
		// return elk.isConsistent();
		// else
		// return (elk.isConsistent() && hermiT.isConsistent());
	}

	@Override
	public boolean isEntailed(OWLAxiom arg0)
			throws ReasonerInterruptedException,
			UnsupportedEntailmentTypeException, TimeOutException,
			AxiomNotInProfileException, FreshEntitiesException,
			InconsistentOntologyException {

		if (arg0 instanceof OWLSubClassOfAxiom) {
			OWLClassExpression subClass = ((OWLSubClassOfAxiom) arg0)
					.getSubClass();
			OWLClassExpression superClass = ((OWLSubClassOfAxiom) arg0)
					.getSuperClass();
			// if (subClass instanceof OWLClass && superClass instanceof
			// OWLClass)
			if (!subClass.isAnonymous() && !superClass.isAnonymous())
				return getSuperClasses(subClass, false).containsEntity(
						(OWLClass) superClass);
			else {
				LogOutput
						.printNotSupported("Not supported: isEntailed (not atomic classes)");
				return false;
			}
		} else {
			LogOutput
					.printNotSupported("Not supported: isEntailed (not subclassof)");
			return false;
		}
	}

	@Override
	public boolean isEntailed(Set<? extends OWLAxiom> arg0)
			throws ReasonerInterruptedException,
			UnsupportedEntailmentTypeException, TimeOutException,
			AxiomNotInProfileException, FreshEntitiesException,
			InconsistentOntologyException {

		for (OWLAxiom ax : arg0) {
			if (!isEntailed(ax)) { // If any of them fails
				return false;
			}
		}

		return true;

		// LogOutput.printNotSupported("Not supported: isEntailed set of axioms");
		// return false;
	}

	@Override
	public boolean isEntailmentCheckingSupported(AxiomType<?> arg0) {

		if (arg0 == AxiomType.SUBCLASS_OF) {
			// LogOutput.printAlways("SUBCLASS_OF entailments are partially supported");
			return true;
		}
		return false;
	}

	@Override
	public boolean isPrecomputed(InferenceType arg0) {

		// TODO
		if (arg0 == InferenceType.CLASS_HIERARCHY) {
			if (classified != notYetClassified) {
				return true;
			}
		}

		return false;
	}

	@Override
	public boolean isSatisfiable(OWLClassExpression arg0)
			throws ReasonerInterruptedException, TimeOutException,
			ClassExpressionNotInProfileException, FreshEntitiesException,
			InconsistentOntologyException {

		if (arg0 instanceof OWLClass) {
			if (classified == notYetClassified) {
				// extract module for class
				return checkSatisfiability(arg0.asOWLClass());
			} else { // if classified, just check
				return !getUnsatisfiableClasses().contains(arg0.asOWLClass());
			}
		} else {
			// LogOutput.printNotSupported("Not supported: isSatisfiable not atomic class (using HermiT)");
			return checkSatisfiability(arg0);
			// return false;
		}
	}

	@Override
	public void precomputeInferences(InferenceType... inferenceTypes)
			throws ReasonerInterruptedException, TimeOutException,
			InconsistentOntologyException {
		Set<InferenceType> requiredInferences = new HashSet<InferenceType>(
				Arrays.asList(inferenceTypes));

		// TODO Indicate that other inferences are not yet supported
		if (requiredInferences.contains(InferenceType.CLASS_HIERARCHY))
			classifyClasses();
		else
			LogOutput
					.printNotSupported("Not supported precomputeInferences different from InferenceType.CLASS_HIERARCHY");
	}

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

		switch (classified) {
		case classifiedWithElk:
			iog = new InferredOntologyGenerator(lReasoner, gens);
			break;
		case classifiedWithOWL2Reasoner:
			iog = new InferredOntologyGenerator(owl2reasoner, gens);
			break;
		default:
			LogOutput.printAlways("Classification not yet computed");
		}

		iog.fillOntology(man.getOWLDataFactory(), infOnt);

		// Save the inferred ontology.
		OWLDocumentFormatImpl format = new FunctionalSyntaxDocumentFormat();
		man.saveOntology(infOnt, format, IRI.create(outputFile.toURI()));

	}

}
