package org.semanticweb.more.protege;

import org.protege.editor.owl.model.inference.AbstractProtegeOWLReasonerInfo;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.ReasonerProgressMonitor;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;

import org.semanticweb.more.MOReRLrewReasonerFactory;

/**
 * Entry point for Protege reasoner plugin (i.e. Protege Factory). Extends
 * AbstractProtegeOWLReasonerInfo and Implements ProtegePluginInstance
 * 
 * 
 * @author Ernesto Jimenez-Ruiz
 * @author Ana Armas
 *
 */
public class MOReRLrewProtegePluginInstance extends
		AbstractProtegeOWLReasonerInfo {

	protected final OWLReasonerFactory factory = new MOReRLrewReasonerFactory();

	@Override
	public BufferingMode getRecommendedBuffering() {
		return BufferingMode.BUFFERING;
	}

	@Override
	public OWLReasonerFactory getReasonerFactory() {
		return factory;
	}

	@Override
	public void initialise() throws Exception {
	}

	@Override
	public void dispose() throws Exception {
	}

	// Same as AbstractProtegeOWLReasonerInfo. Default configuration and monitor
	public OWLReasonerConfiguration getConfiguration(
			ReasonerProgressMonitor monitor) {
		return new SimpleConfiguration(monitor);
	}

}
