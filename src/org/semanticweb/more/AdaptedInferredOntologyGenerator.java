package org.semanticweb.more;

import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.util.InferredAxiomGenerator;
import org.semanticweb.owlapi.util.InferredEquivalentClassAxiomGenerator;
import org.semanticweb.owlapi.util.InferredOntologyGenerator;
import org.semanticweb.owlapi.util.InferredSubClassAxiomGenerator;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.OWLOntologyChangeException;

import java.util.Set;
import java.util.HashSet;
import java.util.List;
import java.util.ArrayList;

/**
 * 
 * Based on org.semanticweb.owlapi.util.InferredOntologyGenerator
 *
 */
public class AdaptedInferredOntologyGenerator {

	// private Set<OWLAxiom> inferredAxioms = new HashSet<OWLAxiom>();

	// The reasoner which is used to compute the inferred axioms
	private final OWLReasoner reasoner;

	private final List<InferredAxiomGenerator<? extends OWLAxiom>> axiomGenerators;

	public AdaptedInferredOntologyGenerator(OWLReasoner reasoner,
			List<InferredAxiomGenerator<? extends OWLAxiom>> axiomGenerators) {
		this.reasoner = reasoner;
		this.axiomGenerators = new ArrayList<InferredAxiomGenerator<? extends OWLAxiom>>(
				axiomGenerators);
	}

	/**
	 * Default constructor. It only includes the
	 * InferredEquivalentClassAxiomGenerator and InferredSubClassAxiomGenerator
	 * generators
	 * 
	 * @param reasoner
	 */
	public AdaptedInferredOntologyGenerator(OWLReasoner reasoner) {
		this.reasoner = reasoner;
		axiomGenerators = new ArrayList<InferredAxiomGenerator<? extends OWLAxiom>>();
		axiomGenerators.add(new InferredEquivalentClassAxiomGenerator());
		axiomGenerators.add(new InferredSubClassAxiomGenerator());
	}

	public void fillInferredAxioms(Set<OWLAxiom> inferredAxioms) {
		fillInferredAxioms(OWLManager.createOWLOntologyManager(),
				inferredAxioms);
	}

	public void fillInferredAxioms(OWLOntologyManager manager,
			Set<OWLAxiom> inferredAxioms) {

		axiomGenerators.stream().forEach((axiomGenerator) -> {
			// inferredAxioms.addAll(axiomGenerator.createAxioms(manager,
			// reasoner));
				axiomGenerator
						.createAxioms(manager.getOWLDataFactory(), reasoner)
						.stream().forEach((ax) -> {
							inferredAxioms.add(ax);
						});
			});
	}

	/**
	 * Reused from InferredOntologyGenerator
	 * 
	 * @param manager
	 * @param ontology
	 * @throws OWLOntologyChangeException
	 */
	public void fillOntology(OWLOntologyManager manager, OWLOntology ontology)
			throws OWLOntologyChangeException {
		List<OWLOntologyChange> changes = new ArrayList<>();
		axiomGenerators.stream()
				.forEach(
						(axiomGenerator) -> {
							axiomGenerator
									.createAxioms(manager.getOWLDataFactory(),
											reasoner)
									.stream()
									.forEach(
											(ax) -> {
												changes.add(new AddAxiom(
														ontology, ax));
											});
						});
		manager.applyChanges(changes);
	}

}
