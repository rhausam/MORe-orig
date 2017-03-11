package org.semanticweb.more.orechallenge;

import org.semanticweb.more.OWL2ReasonerManager;
import org.semanticweb.more.MOReReasoner;
import org.semanticweb.more.io.LogOutput;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

public class MORePelletReasonerWrapper extends MOReReasonerWrapper {

	public MORePelletReasonerWrapper(OWLOntology ont) {
		super(ont);
	}

	/**
	 * Create a reasoner instance. In this case, an instance of MORe using
	 * Pellet
	 * 
	 * @return Reasoner instance
	 */
	public OWLReasoner createReasoner() {
		LogOutput.showOutpuLog(false);
		MOReReasoner MORe = new MOReReasoner(ont);
		MORe.setReasoner(OWL2ReasonerManager.PELLET);
		return MORe;
	}

	/**
	 * Create a reasoner instance. In this case, an instance of MORe using
	 * Pellet
	 * 
	 * @param onto
	 *            We give a concrete ontology (e.g. module for a given class C)
	 * @return Reasoner instance
	 */
	public OWLReasoner createReasoner(OWLOntology onto) {
		LogOutput.showOutpuLog(false);
		MOReReasoner MORe = new MOReReasoner(onto);
		MORe.setReasoner(OWL2ReasonerManager.PELLET);
		return MORe;
	}

	/**
	 * @param args
	 * @throws OWLOntologyCreationException
	 */
	public static void main(String[] args) throws OWLOntologyCreationException {

		main_method(args, OWL2ReasonerManager.PELLET);

	}

}
