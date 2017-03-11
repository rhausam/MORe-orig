package org.semanticweb.more.hermit;

import java.util.Set;

import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.graph.Graph;
import org.semanticweb.HermiT.hierarchy.ClassificationProgressMonitor;
import org.semanticweb.HermiT.hierarchy.Hierarchy;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.tableau.Tableau;
import org.semanticweb.owlapi.model.OWLOntology;

public class HermiTforMORe extends Reasoner {

	// this is an adaptation of HermiT to allow for exploitation of a
	// precomputed set of
	// possible subsumptions for a certain subsignature, and the complete set of
	// subsumptions
	// for the remaining signature.

	protected static Graph<AtomicConcept> m_poss;
	protected static Graph<AtomicConcept> m_known;

	public HermiTforMORe(OWLOntology rootOntology,
			Graph<AtomicConcept> possibleSubsumtions,
			Graph<AtomicConcept> knownSubsumtions) {
		super(new Configuration(), rootOntology);
		m_poss = possibleSubsumtions;
		m_known = knownSubsumtions;
	}

	@Override
	protected Hierarchy<AtomicConcept> classifyAtomicConcepts(Tableau tableau,
			ClassificationProgressMonitor progressMonitor,
			AtomicConcept topElement, AtomicConcept bottomElement,
			Set<AtomicConcept> elements, boolean forceQuasiOrder) {
		return new QuasiOrderClassificationForMORe(tableau, progressMonitor,
				topElement, bottomElement, elements, m_poss, m_known)
				.classify();
	}

}
