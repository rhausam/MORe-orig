package org.semanticweb.more;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
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
import org.semanticweb.more.RLrewriting.RLOntology;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class MOReReasonerWithRLandMaterializationByStages extends MOReRLrew {

	public MOReReasonerWithRLandMaterializationByStages(OWLOntology ontology)
			throws OWLOntologyCreationException {
		super(ontology);
	}

	@Override
	protected Graph<AtomicConcept> computeUpperBoundClassification(
			OWLOntology ontology) {

		// Rewrite the given ontology into owl2rl
		String ontologyName = manager.getOntologyDocumentIRI(ontology)
				.toString();
		String[] chunks = ontologyName.split("/");
		for (String s : chunks)
			if (s.contains(".owl") || s.contains(".obo"))
				ontologyName = s;
		String ontologyLocation = manager.getOntologyDocumentIRI(ontology)
				.toString().replaceFirst("/" + ontologyName, "")
				.replaceFirst("file:", "");

		timeForRLrewriting = System.currentTimeMillis();
		RLOntology rlOntology = new RLOntology(ontologyLocation, ontologyName,
				true);
		rlOntology.transform();
		OWLOntology rewrittenOntology = rlOntology.getOutputOntology();
		timeForRLrewriting = System.currentTimeMillis() - timeForRLrewriting;

		OWLDataFactory factory = new OWLDataFactoryImpl();
		// Set<OWLNamedIndividual> individuals = new
		// HashSet<OWLNamedIndividual>();
		Set<OWLAxiom> newABoxAxioms = new HashSet<OWLAxiom>();
		Map<Individual, AtomicConcept> conceptsForIndividuals = new HashMap<Individual, AtomicConcept>();
		Map<Individual, org.semanticweb.HermiT.tableau.Node> nodesForIndividuals = new HashMap<Individual, org.semanticweb.HermiT.tableau.Node>();
		// Map<AtomicConcept,OWLClass> conceptsForClasses = new
		// HashMap<AtomicConcept, OWLClass>();

		// Introduce an ABox assertion for each concept outside the Lsignature -
		// in groups of up to 10.000
		int counter = 0;
		Reasoner hermiT;
		Tableau tableau;
		Graph<AtomicConcept> candidateSubsumers = new Graph<AtomicConcept>();
		Iterator<OWLEntity> iter = compSignature.iterator();
		OWLEntity e;
		// for (OWLEntity e : compSignature){
		while (iter.hasNext()) {
			e = iter.next();
			if (e instanceof OWLClass) {

				counter++;

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
								.getOWLNamedIndividual(IRI.create(owlIndName));
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

			if (counter == 10000 || !iter.hasNext()) {

				manager.addAxioms(rewrittenOntology, newABoxAxioms);

				Configuration config = new Configuration();
				hermiT = new Reasoner(config, rewrittenOntology);
				tableau = hermiT.getTableau();

				System.out.println("hermit is materialising");
				if (tableau.isSatisfiable(true, false, new HashSet<Atom>(),
						new HashSet<Atom>(), new HashSet<Atom>(),
						new HashSet<Atom>(), nodesForIndividuals,
						ReasoningTaskDescription.isABoxSatisfiable())) {

					System.out
							.println("hermit has finished partially materialising");

					ExtensionManager em = tableau.getExtensionManager();
					ExtensionTable bet = em.getBinaryExtensionTable();
					Retrieval ret = bet.createRetrieval(new boolean[] { false,
							true }, ExtensionTable.View.EXTENSION_THIS);
					for (Individual i : nodesForIndividuals.keySet()) {
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
				}

				counter = 0;
				manager.removeAxioms(rewrittenOntology, newABoxAxioms);
				newABoxAxioms = new HashSet<OWLAxiom>();
				conceptsForIndividuals = new HashMap<Individual, AtomicConcept>();
				nodesForIndividuals = new HashMap<Individual, org.semanticweb.HermiT.tableau.Node>();
			}

		}

		System.out.println("all candidate subsumers have been retrieved now");

		return candidateSubsumers;
	}

	// protected Graph<AtomicConcept>
	// computeUpperBoundClassification(OWLOntology ontology){
	// OWLDataFactory factory = new OWLDataFactoryImpl();
	// Set<OWLNamedIndividual> individuals = new HashSet<OWLNamedIndividual>();
	//
	// //rewrite the given ontology into owl2rl
	// String ontologyName =
	// manager.getOntologyDocumentIRI(ontology).toString();
	// String[] chunks = ontologyName.split("/");
	// for (String s : chunks)
	// if (s.contains(".owl") || s.contains(".obo"))
	// ontologyName = s;
	// String ontologyLocation =
	// manager.getOntologyDocumentIRI(ontology).toString().replaceFirst("/"+ontologyName,
	// "").replaceFirst("file:", "");
	//
	// timeForRLrewriting = System.currentTimeMillis();
	// System.out.println(ontologyLocation);
	// System.out.println(ontologyName);
	// RLOntology rlOntology = new RLOntology(ontologyLocation, ontologyName,
	// true);
	// rlOntology.transform();
	// OWLOntology rewrittenOntology = rlOntology.getOutputOntology();
	// timeForRLrewriting = System.currentTimeMillis() - timeForRLrewriting;
	// // try {
	// //
	// System.out.println(rewrittenOntology.getOntologyID().getOntologyIRI());
	// //
	// manager.loadOntology(rewrittenOntology.getOntologyID().getOntologyIRI());
	// // } catch (OWLOntologyCreationException e1) {
	// // e1.printStackTrace();
	// // }
	//
	// Graph<AtomicConcept> candidateSubsumers = new Graph<AtomicConcept>();
	//
	// //Introduce an ABox assertion for each concept outside the Lsignature
	// //and materialize the ontology with just one of these ABox assertions at
	// a time
	// timeForMaterialization = System.currentTimeMillis();
	// for (OWLEntity e : compSignature){
	//
	// if (e instanceof OWLClass){
	// String[] s;
	// if (e.toString().contains("#"))
	// s = e.toString().split("#");
	// else
	// s = e.toString().split("/");
	// for (String subSt : s)
	// if (subSt.contains(">")){
	// String owlIndName = new
	// String(e.toString().replace("<","").replace(subSt, "ind" +
	// subSt.replaceAll(">", "")));
	// OWLNamedIndividual owlInd =
	// factory.getOWLNamedIndividual(IRI.create(owlIndName));
	// individuals.add(owlInd);
	// OWLAxiom ax = factory.getOWLClassAssertionAxiom((OWLClass) e, owlInd);
	// manager.addAxiom(rewrittenOntology, ax);
	//
	// Individual ind = Individual.create(owlInd.getIRI().toString());
	// AtomicConcept ac = AtomicConcept.create(e.getIRI().toString());
	// HashMap<Individual, org.semanticweb.HermiT.tableau.Node>
	// nodesForIndividuals = new HashMap<Individual,
	// org.semanticweb.HermiT.tableau.Node>();
	// nodesForIndividuals.put(ind, null);
	//
	// //now we have HermiT realize the ontology
	// // Reasoner hermiT = new Reasoner(rlOntology.getOutputOntology());
	// Tableau tableau = new
	// Reasoner(rlOntology.getOutputOntology()).getTableau();
	//
	//
	// // System.out.println(finalOutputMessage);
	//
	// if (tableau.isSatisfiable(
	// true,
	// false,
	// new HashSet<Atom>(),
	// new HashSet<Atom>(),
	// new HashSet<Atom>(),
	// new HashSet<Atom>(),
	// nodesForIndividuals,
	// ReasoningTaskDescription.isABoxSatisfiable())){
	//
	// ExtensionManager em = tableau.getExtensionManager();
	// ExtensionTable bet = em.getBinaryExtensionTable();
	// Retrieval ret = bet.createRetrieval(
	// new boolean[] {false, true},
	// ExtensionTable.View.EXTENSION_THIS);
	// ret.getBindingsBuffer()[1] =
	// nodesForIndividuals.get(ind).getCanonicalNode();
	// ret.open();
	// while (!ret.afterLast()) {
	// Object co = ret.getTupleBuffer()[0];
	// if ((co instanceof AtomicConcept && !co.toString().contains("internal"))
	// && !co.toString().contains("#TOP>"))
	// candidateSubsumers.addEdge(ac, (AtomicConcept) co);
	// ret.next();
	// }
	// }
	// tableau = null;
	// manager.removeAxiom(rewrittenOntology, ax);
	// }
	// }
	// }
	// timeForMaterialization = System.currentTimeMillis() -
	// timeForMaterialization;
	// System.out.println("hermit has finished materialising in " +
	// timeForMaterialization + " milliseconds");
	// return candidateSubsumers;
	// }
}
