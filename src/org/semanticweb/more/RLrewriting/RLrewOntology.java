package org.semanticweb.more.RLrewriting;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/**
 * This class extends RLOntology so that the intermediate ontologies are not
 * stored
 * 
 * @author root
 *
 */
public class RLrewOntology extends RLOntology {

	private String rlOntologyIRI;

	public RLrewOntology(OWLOntologyManager manager, OWLOntology onto,
			boolean flag) {
		super();

		this.manager = manager;
		removeBottomRule = flag;
		factory = manager.getOWLDataFactory();

		try {
			inputOntology = onto;

			ontologyIRI = inputOntology.getOntologyID().getOntologyIRI()
					.toString();
			manager.clearIRIMappers();
			TOP = factory.getOWLClass(IRI.create(ontologyIRI + "#TOP"));

			rlOntologyIRI = ontologyIRI.replaceFirst(".owl", "-rl.owl");
			// System.out.println("rlOntologyIRI is " + rlOntologyIRI);
			if (!rlOntologyIRI.contains("-rl.owl")) {
				if (!rlOntologyIRI.endsWith("#")) {
					rlOntologyIRI += "-rl.owl";
				} else {
					// int i = rlOntologyIRI.lastIndexOf("#");
					rlOntologyIRI = ontologyIRI.replaceFirst("#", "");
				}

			}
			// System.out.println("rlDocumentIRI now is " + rlOntologyIRI);
			// String rlOntologyIRI = ontologyIRI.replaceFirst(".obo",
			// "-rl.obo"); //by Ana
			// System.out.println(rlOntologyIRI);//by Ana

			outputOntology = manager.createOntology(IRI.create(rlOntologyIRI));

			interOntology = manager.createOntology();
			restOntology = manager.createOntology();
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}

	}

	public String getIRIRewirtenOntology() {
		return rlOntologyIRI;
	}

	public void transform() {
		simplifyABox();

		/**
		 * TODO: for dealing with nominals, we should also add the following
		 * axioms for each introduced R to the ontology: dom(R) \sqsubseteq TOP,
		 * ran(R) \subseteq TOP
		 */
		for (OWLOntology ontology : interOntology.getImportsClosure()) {
			for (OWLClass c : ontology.getClassesInSignature()) {
				if (!c.equals(factory.getOWLThing()))
					addAxiom2output(factory.getOWLSubClassOfAxiom(c, TOP));
				else
					addAxiom2output(factory.getOWLSubClassOfAxiom(TOP, c));
			}
			for (OWLObjectProperty p : ontology
					.getObjectPropertiesInSignature()) {
				addAxiom2output(factory.getOWLObjectPropertyDomainAxiom(p, TOP));
				addAxiom2output(factory.getOWLObjectPropertyRangeAxiom(p, TOP));
			}
		}

		seperate();
		clausify();

		// int counter = 0;
		subCounter = new HashMap<OWLClassExpression, Integer>();
		Set<Clause> clauses = new HashSet<Clause>();
		for (DLClause c : dlOntology.getDLClauses()) {
			// System.out.println(++counter);
			// if (c.toString().contains("Employee") ||
			// c.toString().contains("PeopleWithHobby"))
			// System.out.println(c.toString());
			Clause clause = new Clause(this, c);
			// System.out.println(simplify(c.toString()) + "\n" +
			// simplify(clause.toString()) +
			// "\n--------------------------------------\n");
			clauses.add(clause);

			/*
			 * count the expressions in the left
			 */
			for (OWLClassExpression exp : clause.getSubClasses()) {
				// add2SubCounter(exp);
				if (exp instanceof OWLClass)
					add2SubCounter(exp);
				else if (exp instanceof OWLObjectSomeValuesFrom) {
					OWLObjectSomeValuesFrom someValue = (OWLObjectSomeValuesFrom) exp;
					add2SubCounter(factory.getOWLObjectSomeValuesFrom(
							someValue.getProperty(), factory.getOWLThing()));
					add2SubCounter(someValue.getFiller());
				} else if (exp instanceof OWLObjectMinCardinality) {
					OWLObjectMinCardinality minCard = (OWLObjectMinCardinality) exp;
					add2SubCounter(factory.getOWLObjectSomeValuesFrom(
							minCard.getProperty(), factory.getOWLThing()));
					add2SubCounter(minCard.getFiller());
				} else {
					// System.out.println("strange  " + exp);
				}

			}
		}

		OWLClassExpression subExp;
		for (Clause clause : clauses) {
			// if (clause.getSubClass().toString().contains("GraduateStudent"))
			// {
			// System.out.println("daf  " + clause.toString());
			// System.out.println("----------------");
			// }
			// if (clause.getSuperClasses().size() != 1)
			// System.out.println(clause.toString());
			// if (clause.getSubClass().toString().contains("Thing")) {
			// System.out.println(clause.toString());
			// }
			subExp = getSimplifiedConjunction(clause.getSubClasses());
			if (subExp.equals(factory.getOWLThing()))
				subExp = TOP;

			for (OWLClassExpression exp : getDisjunctionApprox0(clause
					.getSuperClasses()))
				addAxiom2output(factory.getOWLSubClassOfAxiom(subExp,
						transform(exp)));
			// addAxiom2output(factory.getOWLSubClassOfAxiom(clause.getSubClass(),
			// factory.getOWLObjectUnionOf(clause.getSuperClasses())));
		}

		clauses.clear();
		subCounter.clear();
	}

	public void clearIntermediateOntologies() {
		manager.removeOntology(restOntology);
		manager.removeOntology(interOntology);
	}

}
