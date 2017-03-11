package org.semanticweb.more.cli;

import java.io.File;
import java.io.FileNotFoundException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.more.OWL2ReasonerManager;
import org.semanticweb.more.MOReReasoner;
import org.semanticweb.more.MOReRLrew;
import org.semanticweb.more.io.LogOutput;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator;

public class MORe_cli {

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
	public static String serializeClassificationResults(
			Set<? extends OWLAxiom> results, OWLOntologyManager man,
			String outFile) {
		File output = new File(outFile);
		output.getParentFile().mkdirs();
		IRI iri = IRI.create("file:" + output.getAbsolutePath());
		try {
			man.saveOntology(man.createOntology((Set<OWLAxiom>) results, iri),
					new FunctionalSyntaxDocumentFormat(), iri);
		} catch (OWLOntologyStorageException e) {
			e.printStackTrace();
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		return iri.toString();
	}

	private static String getHelpMessage() {
		return "\nMORe-cli (v. 0.1.5) requires 4 parameters.\n\n"
				+ "\t1. MORe variant: MORe-A-HermiT (or HermiT), MORe-A-JFact (or jfact) and MORe-B-experimental (or Exp).\n"
				+ "\t2. Location kind of the ontology: e.g.: \"uri\" or \"file\"\n"
				+ "\t3. Ontology File or Ontology URI. e.g.: /home/ernesto/test/ontos/pizza.owl (file)  or  test/ontos/pizza.owl (relative file)  or  http://myonto2.owl (uri)  or  file:/C://myonto2.owl (local uri) or  file:/usr/local/myonto2.owl (local uri) \n"
				+ "\t4. Path (absoulte or relative) for the output classification file (OWL format)\n\n"
				+ "For example: java -jar MORe.standalone.jar HermiT uri file:/home/ontologies/nciOncology-03.09d-new.owl /home/ernesto/test/output/nci-classification.owl\n\n"
				+ "For example: java -jar MORe.standalone.jar JFact file /home/ontologies/nciOncology-03.09d-new.owl /home/ernesto/test/output/nci-classification.owl\n\n"
				+ "For example: java -jar MORe.standalone.jar Exp uri http://krono.act.uji.es/Links/ontologies/nciOncology-03.09d-new.owl /home/ernesto/test/output/nci-classification.owl\n\n"
				+ "These JVM paremeters may also be necessary for large ontologies: -Xms500M -Xmx4400M -DentityExpansionLimit=100000000\n\n";
	}

	public static void main(String[] args) throws FileNotFoundException,
			OWLOntologyStorageException {

		if (args.length != 4) {
			System.out.println(getHelpMessage());
			return;
		}

		LogOutput.showOutpuLog(false);

		OWLOntologyManager man = OWLManager.createOWLOntologyManager();
		OWLOntology ont;
		ThreadMXBean bean;

		String dl_reasoner = args[0]; // Pellet, Hermit
		String op = args[1]; // uri or file
		String ontFile = args[2]; // ontology file
		String outFile = args[3]; // output file classification

		bean = ManagementFactory.getThreadMXBean();

		if (!dl_reasoner.toLowerCase().contains("jfact")
				&& !dl_reasoner.toLowerCase().contains("hermit")
				&& !dl_reasoner.toLowerCase().contains("exp")) {
			System.out.println("\nPlease indicate a proper MORe variant.\n\n"
					+ getHelpMessage());
			return;
		}

		try {

			// Load ontology from URI or file
			if (op.equalsIgnoreCase("uri")) {
				ont = man.loadOntology(IRI.create(ontFile));
			} else { // file
				File f = new File(ontFile);
				ont = man.loadOntologyFromOntologyDocument(f.getAbsoluteFile());
			}

			long start = bean.getCurrentThreadCpuTime();
			long start_wc = System.nanoTime();

			MOReReasoner MORe;

			/*
			 * if(dl_reasoner.toLowerCase().contains("pellet")) { MORe = new
			 * MOReReasoner(ont); MORe.setReasoner(OWL2ReasonerManager.PELLET);
			 * System.out.println("Classifying ontology " + ontFile +
			 * " with MORe-A-Pellet"); }
			 */
			if (dl_reasoner.toLowerCase().contains("jfact")) {
				MORe = new MOReReasoner(ont);
				MORe.setReasoner(OWL2ReasonerManager.FACTPP);
				System.out.println("Classifying ontology " + ontFile
						+ " with MORe-A-JFact " + MORe.getReasonerVersionStr());
			} else if (dl_reasoner.toLowerCase().contains("hermit")) {
				MORe = new MOReReasoner(ont);
				MORe.setReasoner(OWL2ReasonerManager.HERMIT);
				System.out
						.println("Classifying ontology " + ontFile
								+ " with MORe-A-HermiT "
								+ MORe.getReasonerVersionStr());
			} else if (dl_reasoner.toLowerCase().contains("exp")) {
				MORe = new MOReRLrew(ont);
				System.out.println("Classifying ontology " + ontFile
						+ " with MORe-B-Experimental "
						+ MORe.getReasonerVersionStr());
			} else {
				System.out.println("Please indicate a proper MORe variant.\n\n"
						+ getHelpMessage());
				return;
			}

			InferredSubClassAxiomGenerator gen = new InferredSubClassAxiomGenerator();

			MORe.precomputeInferences(InferenceType.CLASS_HIERARCHY);

			long end = bean.getCurrentThreadCpuTime();
			long end_wc = System.nanoTime();

			System.out.println("\tOperation time: " + (end_wc - start_wc)
					/ 1000000000.0);
			System.out.println("\tOperation CPU time: " + (end - start)
					/ 1000000000.0);

			Set<OWLSubClassOfAxiom> result_class = gen.createAxioms(
					man.getOWLDataFactory(), MORe);

			MORe.dispose();

			// We output the classification (i.e. subclassof axioms) as an OWL
			// ontology
			serializeClassificationResults(result_class, man, outFile);
			System.out.println("\tClassification output stored in " + outFile);

		} catch (Exception e) {
			e.printStackTrace();
		}

	}

}
