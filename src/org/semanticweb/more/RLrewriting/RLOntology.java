package org.semanticweb.more.RLrewriting;

import java.io.File;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import com.google.common.base.Optional;

import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLOntology;
import org.semanticweb.HermiT.structural.OWLClausification;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

public class RLOntology {

	OWLOntologyManager manager;
	OWLDataFactory factory;
	String ontologyIRI;
	OWLOntology inputOntology = null;
	OWLOntology interOntology = null;
	OWLOntology restOntology = null;
	OWLOntology outputOntology = null;
	OWLClass TOP;

	DLOntology dlOntology = null;
	int rlCounter = 0;
	boolean removeBottomRule;

	public RLOntology() {

	}

	public RLOntology(String directory, String ontologyName, boolean flag) {
		removeBottomRule = flag;
		manager = OWLManager.createOWLOntologyManager();
		factory = manager.getOWLDataFactory();

		try {
			String documentIRI;
			inputOntology = manager.loadOntologyFromOntologyDocument(new File(
					documentIRI = directory + "/" + ontologyName));
			ontologyIRI = inputOntology.getOntologyID().getOntologyIRI().get()
					.toString();
			manager.clearIRIMappers();
			TOP = factory.getOWLClass(IRI.create(ontologyIRI + "#TOP"));

			String rlOntologyIRI = ontologyIRI.replaceFirst(".owl", "-rl.owl");
			if (!rlOntologyIRI.contains("-rl.owl")) {
				if (!rlOntologyIRI.endsWith("#")) {
					rlOntologyIRI += "-rl.owl";
				} else {
					// int i = rlOntologyIRI.lastIndexOf("#");
					rlOntologyIRI = ontologyIRI.replaceFirst("#", "");
				}

			}
			// String rlOntologyIRI = ontologyIRI.replaceFirst(".obo",
			// "-rl.obo"); //by Ana

			// System.out.println(rlOntologyIRI);//by Ana

			String rlDocumentIRI = "file:"
					+ documentIRI.replaceFirst("input", "output").replaceFirst(
							".owl", "-rl.owl");
			if (!rlDocumentIRI.contains("-rl.owl")) {
				rlDocumentIRI += "-rl.owl";
			}
			// String rlDocumentIRI = "file:/" +
			// documentIRI.replaceFirst("input", "output").replaceFirst(".obo",
			// "-rl.obo"); //by Ana

			outputOntology = manager.createOntology(IRI.create(rlOntologyIRI));
			manager.setOntologyDocumentIRI(outputOntology,
					IRI.create(rlDocumentIRI));

			interOntology = manager.createOntology();
			restOntology = manager.createOntology();
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
	}

	protected void add2SubCounter(OWLClassExpression exp) {
		Integer count = subCounter.get(exp);
		if (count == null)
			count = 0;
		++count;
		subCounter.put(exp, count);
	}

	public void simplify() {
		simplifyABox();
		save(interOntology);
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
				}
				// else
				// System.out.println("strange  " + exp);

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
		save(outputOntology);
	}

	protected String simplify(String str) {
		return str.replace("http://www.w3.org/TR/2003/CR-owl-guide-20030818/",
				"");
	}

	protected void save(OWLOntology onto) {
		try {
			manager.saveOntology(onto);
		} catch (OWLOntologyStorageException e) {
			e.printStackTrace();
		}
	}

	/*
	 * treat disjunction as conjunction
	 */
	protected Set<OWLClassExpression> getDisjunctionApprox0(
			Set<OWLClassExpression> superClasses) {
		return superClasses;
	}

	/*
	 * choose one simple class disjunct
	 */
	private Set<OWLClassExpression> getDisjunctionApprox1(
			Set<OWLClassExpression> superClasses) {
		if (superClasses.isEmpty() || superClasses.size() == 1)
			return superClasses;

		OWLClassExpression rep = null;
		int min = Integer.MAX_VALUE, o;
		for (OWLClassExpression exp : superClasses)
			if (exp instanceof OWLClass && (o = getOccurrence(exp)) < min) {
				min = o;
				rep = exp;
			}

		if (rep == null)
			rep = superClasses.iterator().next();

		return Collections.singleton(rep);
	}

	Random random = new Random(19900114);

	/*
	 * randomly choose a class expression to represent this disjunction
	 */
	private Set<OWLClassExpression> getDisjunctionApprox2(
			Set<OWLClassExpression> superClasses) {
		if (superClasses.isEmpty() || superClasses.size() == 1)
			return superClasses;

		int index = random.nextInt() % superClasses.size();
		if (index < 0)
			index += superClasses.size();

		int i = 0;
		for (OWLClassExpression exp : superClasses)
			if (i++ == index)
				return Collections.singleton(exp);
		return null;
	}

	protected Map<OWLClassExpression, Integer> subCounter = null;

	/*
	 * choose the one that appears least in the l.h.s.
	 */
	private Set<OWLClassExpression> getDisjunctionApprox3(
			Set<OWLClassExpression> superClasses) {
		if (superClasses.isEmpty() || superClasses.size() == 1)
			return superClasses;

		OWLClassExpression rep = null, exp1;
		int occurrence = Integer.MAX_VALUE, o;
		for (OWLClassExpression exp : superClasses) {
			o = 0;
			exp1 = exp;
			if (exp instanceof OWLObjectMinCardinality) {
				OWLObjectMinCardinality minCard = (OWLObjectMinCardinality) exp;
				if (minCard.getCardinality() == 1)
					exp1 = factory.getOWLObjectSomeValuesFrom(
							minCard.getProperty(), minCard.getFiller());
			}

			if (!subCounter.containsKey(exp1)
					|| (o = subCounter.get(exp1)) < occurrence) {
				rep = exp;
				occurrence = o;
			}
		}

		return Collections.singleton(rep);
	}

	private int getOccurrence(OWLClassExpression exp) {
		if (!subCounter.containsKey(exp))
			return 0;
		return subCounter.get(exp);
	}

	private Set<OWLClassExpression> getDisjunctionApprox4(
			Set<OWLClassExpression> superClasses) {
		if (superClasses.isEmpty() || superClasses.size() == 1)
			return superClasses;

		OWLClassExpression rep = null;
		int occurrence = Integer.MAX_VALUE, o;
		for (OWLClassExpression exp : superClasses) {
			o = 0;
			if (exp instanceof OWLObjectMinCardinality) {
				OWLObjectMinCardinality minCard = (OWLObjectMinCardinality) exp;
				if (minCard.getCardinality() == 1) {
					o = getOccurrence((factory.getOWLObjectSomeValuesFrom(
							minCard.getProperty(), factory.getOWLThing())));
					o += getOccurrence(minCard.getFiller());
					// if (o < o1) o = o1;
				}
			} else
				o = getOccurrence(exp);

			if (o < occurrence || o == occurrence && !(rep instanceof OWLClass)) {
				rep = exp;
				occurrence = o;
			}
		}

		return Collections.singleton(rep);
	}

	// by Ana: this method introduces alias for complex class expressions in
	// order to rewrite into the appropriate normal form(??)
	protected void simplifyABox() {
		Map<OWLClassExpression, OWLClass> complex2atomic = new HashMap<OWLClassExpression, OWLClass>();

		for (OWLOntology imported : inputOntology.getImportsClosure())
			for (OWLAxiom axiom : imported.getAxioms()) {

				if (axiom instanceof OWLClassAssertionAxiom) {
					OWLClassAssertionAxiom assertion = (OWLClassAssertionAxiom) axiom;
					OWLClassExpression clsExp = assertion.getClassExpression();
					OWLClass cls;
					if (clsExp instanceof OWLClass)
						manager.addAxiom(interOntology, axiom);
					else {
						if ((cls = complex2atomic.get(clsExp)) == null) {
							complex2atomic
									.put(clsExp,
											cls = factory.getOWLClass(IRI
													.create(getNewConcept(rlCounter++))));
							manager.addAxiom(interOntology,
									factory.getOWLSubClassOfAxiom(cls, clsExp));
						}
						manager.addAxiom(interOntology, factory
								.getOWLClassAssertionAxiom(cls,
										assertion.getIndividual()));
					}
				} else
					manager.addAxiom(interOntology, axiom);
			}
	}

	protected void seperate() {
		RLChecker checker = new RLChecker();
		// int counter = 0;
		for (OWLOntology imported : interOntology.getImportsClosure())
			for (OWLAxiom axiom : imported.getAxioms()) {
				if (removeBottomRule
						&& axiom instanceof OWLDisjointClassesAxiom) {
					// System.out.println(axiom);
					continue;
				}
				if (checker.check(axiom)) {
					// System.out.println("yes");
					addAxiom2output(axiom);
				} else {
					// System.out.println(++counter);
					// System.out.println(simplify(axiom.toString()));
					// System.out.println("difficult cases... ");
					manager.addAxiom(restOntology, axiom);
				}
			}
	}

	protected void clausify() {
		// Reasoner hermiT = new Reasoner(restOntology);
		Configuration conf = new Configuration();
		OWLClausification clausifier = new OWLClausification(conf);
		dlOntology = (DLOntology) clausifier.preprocessAndClausify(
				restOntology, null)[1];
		clausifier = null;
	}

	protected void addAxiom2output(OWLAxiom axiom) {
		manager.addAxiom(outputOntology, axiom);
	}

	private Map<OWLClass, OWLClass> atomic2negation = new HashMap<OWLClass, OWLClass>();
	private Map<OWLClassExpression, OWLObjectProperty> exists2role = new HashMap<OWLClassExpression, OWLObjectProperty>();

	protected OWLClassExpression transform(OWLClassExpression exp) {
		if (exp instanceof OWLClass)
			return exp;

		if (exp instanceof OWLObjectHasValue)
			return exp;

		if (exp instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom someValueExp = (OWLObjectSomeValuesFrom) exp;
			/*
			 * OWLObjectProperty r =
			 * factory.getOWLObjectProperty(IRI.create(getNewRole(rlCounter)));
			 * addAxiom2output(factory.getOWLSubObjectPropertyOfAxiom(r,
			 * someValueExp.getProperty())); OWLClassExpression tExp =
			 * someValueExp.getFiller(); if (!(tExp instanceof
			 * OWLObjectComplementOf))
			 * addAxiom2output(factory.getOWLObjectPropertyRangeAxiom(r, tExp));
			 * else if (!removeBottomRule) { OWLClass cls = (OWLClass)
			 * ((OWLObjectComplementOf) tExp).getComplementNNF(); OWLClass neg;
			 * if ((neg = atomic2negation.get(cls)) == null) { neg =
			 * factory.getOWLClass(IRI.create(getNewConcept(rlCounter++)));
			 * addAxiom2output(factory.getOWLDisjointClassesAxiom(neg, cls)); }
			 * addAxiom2output(factory.getOWLObjectPropertyRangeAxiom(r, neg));
			 * System
			 * .out.println("strange situation in Ontology.transform~~~~ 1"); }
			 * 
			 * OWLIndividual c =
			 * factory.getOWLNamedIndividual(IRI.create(getNewIndividual
			 * (rlCounter++))); return factory.getOWLObjectHasValue(r, c);
			 */

			OWLClassExpression tExp = someValueExp.getFiller();
			if (tExp.equals(factory.getOWLThing()))
				exp = factory.getOWLObjectMinCardinality(1,
						someValueExp.getProperty());
			else
				exp = factory.getOWLObjectMinCardinality(1,
						someValueExp.getProperty(), someValueExp.getFiller());
		}

		if (exp instanceof OWLObjectMinCardinality) {
			OWLObjectMinCardinality minExp = (OWLObjectMinCardinality) exp;
			OWLObjectProperty r;
			OWLObjectSomeValuesFrom someValueExp = factory
					.getOWLObjectSomeValuesFrom(minExp.getProperty(),
							minExp.getFiller());

			if ((r = exists2role.get(someValueExp)) == null) {

				// deal with r' \subseteq r & range(r') \subseteq C
				r = factory.getOWLObjectProperty(IRI
						.create(getNewRole(rlCounter)));
				addAxiom2output(factory.getOWLSubObjectPropertyOfAxiom(r,
						minExp.getProperty()));
				OWLClassExpression tExp = minExp.getFiller();
				if (!(tExp instanceof OWLObjectComplementOf)) {
					if (tExp.equals(factory.getOWLThing())) {
						// System.out.println(tExp);
					} else
						addAxiom2output(factory.getOWLObjectPropertyRangeAxiom(
								r, tExp));
				} else if (!removeBottomRule) {
					OWLClass cls = (OWLClass) ((OWLObjectComplementOf) tExp)
							.getComplementNNF();
					OWLClass neg;
					if ((neg = atomic2negation.get(cls)) == null) {
						neg = factory.getOWLClass(IRI
								.create(getNewConcept(rlCounter)));
						addAxiom2output(factory.getOWLDisjointClassesAxiom(neg,
								cls));
						atomic2negation.put(cls, neg);
					}
					addAxiom2output(factory.getOWLObjectPropertyRangeAxiom(r,
							neg));
				}
				exists2role.put(someValueExp, r);
			}

			// deal with r'(x,c)
			Set<OWLClassExpression> ret = new HashSet<OWLClassExpression>();
			int num = minExp.getCardinality();

			Set<OWLNamedIndividual> cs = new HashSet<OWLNamedIndividual>();
			OWLNamedIndividual c;
			for (int i = 0; i < num; ++i) {
				c = factory.getOWLNamedIndividual(IRI
						.create(getNewIndividual(rlCounter++)));
				ret.add(factory.getOWLObjectHasValue(r, c));
				cs.add(c);
			}

			if (!removeBottomRule && cs.size() > 1) {
				addAxiom2output(factory.getOWLDifferentIndividualsAxiom(cs));
			}

			// if (ret.size() == 0)
			// System.out.println("zero min cardinality constraint");
			// else if (ret.size() == 1)
			// return ret.iterator().next();
			// else
			// return factory.getOWLObjectIntersectionOf(ret);
			return getSimplifiedConjunction(ret);
		}

		if (exp instanceof OWLObjectMaxCardinality) {
			OWLObjectMaxCardinality maxExp = (OWLObjectMaxCardinality) exp;
			OWLClassExpression tExp = maxExp.getFiller();
			int card = maxExp.getCardinality() >= 1 ? 1 : 0;
			if (!(tExp instanceof OWLObjectComplementOf))
				return factory.getOWLObjectMaxCardinality(card,
						maxExp.getProperty(), tExp);
			else {
				// System.out.println("oh, to be tested ... ");
				OWLClassExpression tExp1 = factory.getOWLObjectAllValuesFrom(
						maxExp.getProperty(), tExp.getComplementNNF());
				if (card == 0)
					return tExp1;
				else {
					OWLClassExpression tExp2 = factory
							.getOWLObjectMaxCardinality(1, maxExp.getProperty());
					return factory.getOWLObjectIntersectionOf(tExp1, tExp2);
				}
			}
		}

		if (exp instanceof OWLObjectAllValuesFrom)
			return exp;

		if (exp instanceof OWLDataHasValue)
			return exp;

		// TODO: Yujiao - dealing with OWLDataMinCardinality

		if (exp instanceof OWLDataSomeValuesFrom)
			return exp;

		if (exp instanceof OWLDataMinCardinality)
			return exp;

		if (exp instanceof OWLDataMaxCardinality)
			return exp;

		Set<OWLClassExpression> exps = exp.asConjunctSet();
		if (exps.size() == 1 && exps.iterator().next() == exp) {
			// System.out.println(exp);
			System.out.println("error in transform of Ontology~~~~");
			return exp; // To avoid invinit iteration...
		}
		Set<OWLClassExpression> nexps = new HashSet<OWLClassExpression>();
		OWLClassExpression ne;
		boolean changes = false;
		for (OWLClassExpression e : exps) {
			ne = transform(e);
			if (ne != e)
				changes = true;
			nexps.add(ne);
		}
		if (changes)
			return getSimplifiedConjunction(nexps);
		else
			return exp;
	}

	protected OWLClassExpression getSimplifiedConjunction(
			Set<OWLClassExpression> set) {
		if (set.size() == 0)
			return factory.getOWLThing();
		else if (set.size() == 1)
			return set.iterator().next();
		else
			return factory.getOWLObjectIntersectionOf(set);
	}

	private String getNewIndividual(int number) {
		return ontologyIRI + "#NI" + number;
	}

	private String getNewRole(int number) {
		return ontologyIRI + "#NR" + number;
	}

	private String getNewConcept(int number) {
		return ontologyIRI + "#NC" + number;
	}

	public OWLOntologyManager getOWLOntologyManager() {
		return inputOntology.getOWLOntologyManager();
	}

	public OWLOntology getOutputOntology() {
		return outputOntology;
	}

	public OWLOntology getIntermediateOntology() {
		return interOntology;
	}

}
