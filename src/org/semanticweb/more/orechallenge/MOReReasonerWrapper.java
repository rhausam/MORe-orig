package org.semanticweb.more.orechallenge;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.more.OWL2ReasonerManager;
import org.semanticweb.more.MOReReasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator;

import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

/**
 * @author Rafael S. Goncalves <br/>
 * @author Ernesto Jimenez Ruiz (adapted to MORe) <br/>
 *         <p>
 *         A simple OWL API based reasoner wrapper (using the MORe reasoner)
 *         supporting only classification and class sat.
 *         </p>
 */
public abstract class MOReReasonerWrapper {
	protected OWLOntology ont;
	protected ThreadMXBean bean;
	private String errorLog;

	/**
	 * Constructor for a simple reasoner wrapper
	 * 
	 * @param ont
	 *            OWL Ontology
	 */
	public MOReReasonerWrapper(OWLOntology ont) {
		this.ont = ont;
		bean = ManagementFactory.getThreadMXBean();
		errorLog = "";
	}

	public abstract OWLReasoner createReasoner();

	public abstract OWLReasoner createReasoner(OWLOntology ont);

	/**
	 * Classify ontology (transitive closure)
	 * 
	 * @return Set of all inferred atomic subsumptions
	 */
	public Set<OWLSubClassOfAxiom> classify() {
		InferredSubClassAxiomGenerator gen = new InferredSubClassAxiomGenerator();
		OWLOntologyManager man = ont.getOWLOntologyManager();

		long start = bean.getCurrentThreadCpuTime();
		long start_wc = System.nanoTime();

		OWLReasoner MORe = createReasoner();
		MORe.precomputeInferences(InferenceType.CLASS_HIERARCHY);

		Set<OWLSubClassOfAxiom> result = gen.createAxioms(
				man.getOWLDataFactory(), MORe);

		long end = bean.getCurrentThreadCpuTime();
		long end_wc = System.nanoTime();

		result = prune(result);

		System.out.println("\tOperation time: " + (end_wc - start_wc)
				/ 1000000.0);
		System.out
				.println("\tOperation CPU time: " + (end - start) / 1000000.0);

		MORe.dispose();

		return result;
	}

	/**
	 * Satisfiability implemented in Reasoner. Check if given concept is
	 * satisfiable
	 * 
	 * @param c
	 *            Concept
	 * @return
	 */
	public boolean isSatisfiable2(OWLClassExpression c) {

		if (c.isAnonymous()) {
			System.out.println("\tNot supported  sat " + " on "
					+ ont.getOntologyID().getOntologyIRI().toString());
		}

		long start = bean.getCurrentThreadCpuTime();
		long start_wc = System.nanoTime();

		OWLReasoner MORe = createReasoner();

		boolean result = MORe.isSatisfiable(c);

		long end = bean.getCurrentThreadCpuTime();
		long end_wc = System.nanoTime();

		System.out.println("\tOperation time: " + (end_wc - start_wc)
				/ 1000000.0);
		System.out
				.println("\tOperation CPU time: " + (end - start) / 1000000.0);

		MORe.dispose();

		return result;
	}

	/**
	 * Check if given concept is satisfiable. Implemented in wrapper.
	 * 
	 * @param c
	 *            Concept
	 * @return true if concept is satisfiable, false otherwise
	 */
	public boolean isSatisfiable(OWLClassExpression c) {

		boolean result = true;

		if (c.isAnonymous()) {
			System.out.println("\tNot supported  sat " + " on "
					+ ont.getOntologyID().getOntologyIRI().toString());
			return result;
		}

		try {

			long start = bean.getCurrentThreadCpuTime();
			long start_wc = System.nanoTime();

			OWLOntologyManager man = ont.getOWLOntologyManager();
			Set<OWLEntity> signature = new HashSet<OWLEntity>();
			signature.add(c.asOWLClass());
			SyntacticLocalityModuleExtractor botModExtractor = new SyntacticLocalityModuleExtractor(
					man, ont, ModuleType.BOT);

			OWLReasoner MORe = createReasoner(botModExtractor
					.extractAsOntology(
							signature,
							IRI.create("http://org.semanticweb.more.orechallenge/aux_iri")));

			// We classify the module to avoid another extraction
			MORe.precomputeInferences(InferenceType.CLASS_HIERARCHY);
			result = MORe.isSatisfiable(c);
			System.out.println(result);

			long end = bean.getCurrentThreadCpuTime();
			long end_wc = System.nanoTime();

			System.out.println("\tOperation time: " + (end_wc - start_wc)
					/ 1000000.0);
			System.out.println("\tOperation CPU time: " + (end - start)
					/ 1000000.0);

			MORe.dispose();

		} catch (OWLOntologyCreationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return result;
	}

	/**
	 * Remove axioms of the type A => T
	 * 
	 * @param axioms
	 *            Set of axioms
	 * @return Updated set of axioms
	 */
	private Set<OWLSubClassOfAxiom> prune(Set<OWLSubClassOfAxiom> axioms) {
		Set<OWLSubClassOfAxiom> toRemove = new HashSet<OWLSubClassOfAxiom>();
		for (OWLSubClassOfAxiom ax : axioms) {
			if (ax.getSuperClass().equals(
					ont.getOWLOntologyManager().getOWLDataFactory()
							.getOWLThing()))
				toRemove.add(ax);
		}
		axioms.removeAll(toRemove);
		return axioms;
	}

	/**
	 * Serialize classifiation results as an OWL file
	 * 
	 * @param results
	 *            Set of inferred subsumptions
	 * @param man
	 *            OWL Ontology Manager
	 * @param ontDir
	 *            Ontology directory
	 * @param reasonerName
	 *            Reasoner name
	 * @return The file path to where the OWL file was saved
	 */
	@SuppressWarnings("unchecked")
	public String serializeClassificationResults(
			Set<? extends OWLAxiom> results, OWLOntologyManager man,
			String outFile) {
		File output = new File(outFile);
		output.getParentFile().mkdirs();
		IRI iri = IRI.create("file:" + output.getAbsolutePath());
		try {
			man.saveOntology(man.createOntology((Set<OWLAxiom>) results, iri),
					new FunctionalSyntaxDocumentFormat(), iri);
		} catch (OWLOntologyStorageException e) {
			errorLog += e.getStackTrace();
		} catch (OWLOntologyCreationException e) {
			errorLog += e.getStackTrace();
		}
		return iri.toString();
	}

	/**
	 * Serialize the specified string to the given file
	 * 
	 * @param outFile
	 *            Output file path
	 * @param outputString
	 *            Output string
	 */
	public void serializeString(String outFile, String outputString) {
		File output = new File(outFile);
		output.getParentFile().mkdirs();
		FileWriter out;
		try {
			out = new FileWriter(output.getAbsolutePath(), true);
			out.write(outputString + "\n");
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	protected static void main_method(String[] args, int reasoner)
			throws OWLOntologyCreationException {
		String op = args[0];
		String ontFile = args[1];
		String outFile = args[2];

		System.out.println("\tStarted " + op + " on " + ontFile);
		File f = new File(ontFile);
		OWLOntologyManager man = OWLManager.createOWLOntologyManager();
		OWLOntology ont = man.loadOntologyFromOntologyDocument(f
				.getAbsoluteFile());

		MOReReasonerWrapper r;
		if (reasoner == OWL2ReasonerManager.PELLET)
			r = new MORePelletReasonerWrapper(ont);
		else
			r = new MOReHermiTReasonerWrapper(ont);

		if (op.equalsIgnoreCase("classification")) {
			Set<? extends OWLAxiom> results = r.classify();
			r.serializeClassificationResults(results, man, outFile);
			System.out.println("\tCompleted " + op + " on " + ontFile);
		} else if (op.equalsIgnoreCase("sat")) {
			OWLClass c = man.getOWLDataFactory().getOWLClass(
					IRI.create(args[3]));
			r.serializeString(outFile,
					c.getIRI().toString() + "," + r.isSatisfiable(c));
			System.out.println("\tCompleted " + op + " on " + ontFile);
		} else {
			System.out.println("\tNot supported  " + op + " on " + ontFile);
		}

		if (!r.errorLog.equals("")) {
			String outDir = new File(outFile).getParent();
			if (outDir.endsWith(File.separator))
				outDir += File.separator;
			r.serializeString(outDir + "error.txt", r.errorLog);
		}

	}

}