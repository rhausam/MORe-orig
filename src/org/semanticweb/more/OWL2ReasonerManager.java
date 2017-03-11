package org.semanticweb.more;

import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.HermiT.Configuration;

import uk.ac.manchester.cs.factplusplus.owlapiv3.FaCTPlusPlusReasonerFactory;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;

//we access through the protege factory
//import com.clarkparsia.protege.plugin.pellet.PelletReasonerFactory;
//import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
//import org.semanticweb.owlapi.reasoner.BufferingMode;

/**
 * Access to an OWL 2 reasoner. So far only HermiT and Pellet
 * 
 * @author Errnesto
 *
 */
public class OWL2ReasonerManager {

	public final static int HERMIT = 0;
	public final static int PELLET = 1;
	public final static int FACTPP = 2;

	public final static String[] reasoner_name = { "HermiT", "Pellet", "FaCT++" };

	// public static String currentReasonerName = "HermiT";

	public static OWLReasoner createOWL2ReasonerInstance(OWLOntology onto,
			int reasonerID) {

		// currentReasonerName = reasoner_name[reasonerID];

		if (reasonerID == HERMIT) {
			// currentReasonerName = "HermiT";
			// This may avoid the exception due to datatypes outside OWL 2
			// specification
			Configuration conf = new Configuration();
			conf.ignoreUnsupportedDatatypes = true;
			return new Reasoner(conf, onto);
		} else if (reasonerID == FACTPP) {
			// currentReasonerName = "FaCTPlusPlus";
			FaCTPlusPlusReasonerFactory reasonerFactory = new FaCTPlusPlusReasonerFactory();
			return reasonerFactory.createReasoner(onto,
					new SimpleConfiguration());
		}
		/*
		 * else { // (OWL2REASONERNAME == PELLET){{ currentReasonerName =
		 * "Pellet";
		 * 
		 * //return new PelletReasoner(onto, // BufferingMode.BUFFERING);
		 * 
		 * PelletReasonerFactory prf = new PelletReasonerFactory(); return
		 * prf.getReasonerFactory().createReasoner(onto);
		 * 
		 * }
		 */
		else { // Hermit
			Configuration conf = new Configuration();
			conf.ignoreUnsupportedDatatypes = true;
			return new Reasoner(conf, onto);
		}

	}

	public static String getCurrentReasonerName(int reasonerID) {
		return reasoner_name[reasonerID];
	}

}
