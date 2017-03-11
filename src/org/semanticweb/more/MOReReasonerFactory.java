package org.semanticweb.more;

import org.semanticweb.owlapi.model.OWLOntology;

import org.semanticweb.owlapi.reasoner.IllegalConfigurationException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/**
 * Factory for the OWLAPI reasoner implementation of the MORe reasoner.
 * 
 * @author aarmas
 * 
 */
public class MOReReasonerFactory implements OWLReasonerFactory {

	private int owl2reasoner;

	public MOReReasonerFactory(int owl2reasoner) {
		this.owl2reasoner = owl2reasoner;
	}

	@Override
	public String getReasonerName() {
		return MOReReasonerFactory.class.getPackage().getImplementationTitle();
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology) {
		return createMoreReasoner(ontology, false, null);
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology) {
		return createMoreReasoner(ontology, true, null);
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config)
			throws IllegalConfigurationException {
		return createMoreReasoner(ontology, false, config);
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ontology,
			OWLReasonerConfiguration config)
			throws IllegalConfigurationException {
		return createMoreReasoner(ontology, true, config);
	}

	protected MOReReasoner createMoreReasoner(OWLOntology ontology,
			boolean isBufferingMode, OWLReasonerConfiguration config)
			throws IllegalConfigurationException {

		// TODO
		// No difference between buffering and not buffering
		MOReReasoner more = new MOReReasoner(ontology, isBufferingMode, config);
		more.setReasoner(owl2reasoner);

		return more;

	}
}
