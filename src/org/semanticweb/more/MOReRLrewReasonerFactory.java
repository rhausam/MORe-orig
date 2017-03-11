package org.semanticweb.more;

import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.IllegalConfigurationException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/**
 * Factory for the OWLAPI reasoner implementation of the MORe RLrew reasoner.
 * 
 * @author aarmas
 * 
 */
public class MOReRLrewReasonerFactory implements OWLReasonerFactory {

	@Override
	public String getReasonerName() {
		return MOReReasonerFactory.class.getPackage().getImplementationTitle();
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology) {
		return createMoreRLrewReasoner(ontology, false, null);
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology) {
		return createMoreRLrewReasoner(ontology, true, null);
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config)
			throws IllegalConfigurationException {
		return createMoreRLrewReasoner(ontology, false, config);
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config)
			throws IllegalConfigurationException {
		return createMoreRLrewReasoner(ontology, true, config);
	}

	protected MOReReasoner createMoreRLrewReasoner(OWLOntology ontology,
			boolean isBufferingMode, OWLReasonerConfiguration config)
			throws IllegalConfigurationException {

		// TODO
		// No difference between buffering and not buffering
		return new MOReRLrew(ontology, isBufferingMode, config);
	}
}
