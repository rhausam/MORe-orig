package org.semanticweb.more.RLrewriting;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.semanticweb.HermiT.model.AnnotatedEquality;
import org.semanticweb.HermiT.model.AtLeastConcept;
import org.semanticweb.HermiT.model.AtLeastDataRange;
import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.HermiT.model.AtomicConcept;
import org.semanticweb.HermiT.model.AtomicNegationConcept;
import org.semanticweb.HermiT.model.AtomicRole;
import org.semanticweb.HermiT.model.Constant;
import org.semanticweb.HermiT.model.ConstantEnumeration;
import org.semanticweb.HermiT.model.DLClause;
import org.semanticweb.HermiT.model.DLPredicate;
import org.semanticweb.HermiT.model.DatatypeRestriction;
import org.semanticweb.HermiT.model.Equality;
import org.semanticweb.HermiT.model.InternalDatatype;
import org.semanticweb.HermiT.model.InverseRole;
import org.semanticweb.HermiT.model.LiteralConcept;
import org.semanticweb.HermiT.model.LiteralDataRange;
import org.semanticweb.HermiT.model.Role;
import org.semanticweb.HermiT.model.Variable;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntologyManager;

public class Clause {

	Set<Atom> headAtoms;
	Set<Atom> bodyAtoms;

	OWLOntologyManager manager;
	OWLDataFactory factory;
	// OWLClass top = null;

	private Set<OWLClassExpression> superClasses = new HashSet<OWLClassExpression>();
	private Set<OWLClassExpression> subClasses = new HashSet<OWLClassExpression>();

	public Clause(RLOntology ontology, DLClause clause) {
		manager = ontology.getOWLOntologyManager();
		factory = manager.getOWLDataFactory();
		// top = ontology.top;

		headAtoms = Utility.toSet(clause.getHeadAtoms());
		bodyAtoms = Utility.toSet(clause.getBodyAtoms());
		rollingUp();
	}

	private static final Variable X = Variable.create("X");

	private void rollingUp() {
		eliminateEquality();

		Map<Variable, Atom> var2atom = new HashMap<Variable, Atom>();

		getVariableOccurrence(var2atom, headAtoms);
		getVariableOccurrence(var2atom, bodyAtoms);

		DLPredicate predicate;
		Variable W = null;

		Map<Variable, String> nom2iri = new HashMap<Variable, String>();
		for (Atom atom : bodyAtoms) {
			predicate = atom.getDLPredicate();
			if (predicate instanceof AtomicConcept) {
				AtomicConcept concept = (AtomicConcept) predicate;
				Variable v = atom.getArgumentVariable(0);
				if (v == X)
					subClasses.add(factory.getOWLClass(IRI.create(concept
							.getIRI())));
				else if (predicate.toString().startsWith("<internal:nom#"))
					nom2iri.put(v, getIRI4Nominal(concept));
			} else if (predicate instanceof AtomicRole) {
				// TODO: Yujiao - didn't take \exists R.Self into account.
				AtomicRole role = (AtomicRole) predicate;

				OWLObjectPropertyExpression roleExp = factory
						.getOWLObjectProperty(IRI.create(role.getIRI()));
				if ((W = atom.getArgumentVariable(1)) == X) {
					roleExp = roleExp.getInverseProperty();
					W = atom.getArgumentVariable(0);
				}

				AtomicConcept concept;
				OWLClassExpression clsExp = null;
				if (var2atom.containsKey(W)) {
					Atom tAtom = var2atom.get(W);
					concept = (AtomicConcept) tAtom.getDLPredicate();
					clsExp = factory.getOWLClass(IRI.create(concept.getIRI()));
					if (headAtoms.contains(tAtom)) {
						superClasses.add(factory.getOWLObjectAllValuesFrom(
								roleExp, clsExp));
						subClasses.add(addSomeValuesFromAxiom(roleExp,
								factory.getOWLThing()));
					} else
						subClasses.add(addSomeValuesFromAxiom(roleExp, clsExp));
				} else
					subClasses.add(addSomeValuesFromAxiom(roleExp,
							factory.getOWLThing()));
				// subClasses.add(factory.getOWLObjectMinCardinality(1,
				// roleExp));
			}
		}

		OWLObjectPropertyExpression objExp;
		for (Atom atom : headAtoms) {
			predicate = atom.getDLPredicate();
			if (predicate instanceof AtomicConcept) {
				if (atom.getArgumentVariable(0) == X)
					superClasses
							.add(getClassExpression((AtomicConcept) predicate));
			} else if (predicate instanceof AtomicRole) {
				objExp = factory.getOWLObjectProperty(IRI
						.create(((AtomicRole) predicate).getIRI()));
				if ((W = atom.getArgumentVariable(1)) == X) {
					objExp = factory.getOWLObjectInverseOf(objExp);
					W = atom.getArgumentVariable(0);
				}
				superClasses.add(factory.getOWLObjectHasValue(objExp, factory
						.getOWLNamedIndividual(IRI.create(nom2iri.get(W)))));
			} else if (predicate instanceof AtLeastConcept)
				superClasses
						.add(getMinCardinalityExpression((AtLeastConcept) predicate));
			else if (predicate instanceof AtLeastDataRange)
				superClasses
						.add(getDataMinCardinalityExpression((AtLeastDataRange) predicate));
			else {
				System.out.println(atom.toString());
				System.out.println("strange head atoms left here~~~~~");
			}
		}
	}

	private OWLObjectSomeValuesFrom addSomeValuesFromAxiom(
			OWLObjectPropertyExpression roleExp, OWLClassExpression classExp) {
		// TODO: owl:thing v.s. TOP

		// if (classExp.equals(factory.getOWLThing()))
		// return factory.getOWLObjectSomeValuesFrom(roleExp, top);
		// else
		return factory.getOWLObjectSomeValuesFrom(roleExp, classExp);
	}

	private void getVariableOccurrence(Map<Variable, Atom> var2atom,
			Set<Atom> atoms) {
		Set<Variable> variables = new HashSet<Variable>();
		for (Atom atom : atoms) {
			variables.clear();
			atom.getVariables(variables);
			if (variables.size() == 1)
				for (Variable variable : variables)
					if (!variable.equals(X))
						var2atom.put(variable, atom);
		}
	}

	private OWLClassExpression getMinCardinalityExpression(
			AtLeastConcept atLeast) {
		OWLObjectPropertyExpression propExp = getObjectPropertyExpression(atLeast
				.getOnRole());
		OWLClassExpression clsExp = getClassExpression(atLeast.getToConcept());
		return factory.getOWLObjectMinCardinality(atLeast.getNumber(), propExp,
				clsExp);
	}

	private OWLClassExpression getDataMinCardinalityExpression(
			AtLeastDataRange atLeast) {
		OWLDataPropertyExpression propExp = getDataPropertyExpression(atLeast
				.getOnRole());
		OWLDataRange dataRange = getDataRange(atLeast.getToDataRange());
		// System.out.println(dataRange);
		return factory.getOWLDataMinCardinality(atLeast.getNumber(), propExp,
				dataRange);
	}

	public Set<OWLClassExpression> getSuperClasses() {
		return superClasses;
	}

	public Set<OWLClassExpression> getSubClasses() {
		return subClasses;
	}

	// public OWLClassExpression getSubClass() {
	// if (subClasses.isEmpty())
	// return factory.getOWLThing();
	// if (subClasses.size() == 1)
	// return subClasses.iterator().next();
	//
	// return factory.getOWLObjectIntersectionOf(subClasses);
	// }

	private void eliminateEquality() {
		Set<Atom> eHeadAtoms = new HashSet<Atom>();
		Set<Atom> eBodyAtoms = new HashSet<Atom>();
		Set<Variable> eVariables = new HashSet<Variable>();
		Set<Variable> tVariables = new HashSet<Variable>();
		Set<Atom> tAtoms = new HashSet<Atom>();
		seperateEquality4Clause(eBodyAtoms, eHeadAtoms, eVariables);

		/*
		 * remove equalities that are introduced by MaxCardinalityConstraints
		 */
		DLPredicate predicate;
		Set<Variable> mVariables = new HashSet<Variable>();
		OWLObjectMaxCardinality maxCardinality;
		OWLClassExpression exp;

		tAtoms.addAll(eHeadAtoms);
		for (Atom atom : tAtoms) {
			predicate = atom.getDLPredicate();
			if (predicate instanceof AnnotatedEquality) {
				superClasses
						.add(maxCardinality = getMaxCardinalityExpression((AnnotatedEquality) predicate));
				if (!((exp = maxCardinality.getFiller()) instanceof OWLObjectComplementOf))
					subClasses.add(factory.getOWLObjectSomeValuesFrom(
							maxCardinality.getProperty(), exp));
				else
					subClasses
							.add(factory.getOWLObjectSomeValuesFrom(
									maxCardinality.getProperty(),
									factory.getOWLThing()));
				tVariables.clear();
				atom.getVariables(tVariables);
				mVariables.addAll(tVariables);
				eHeadAtoms.remove(atom);
			}
		}

		tAtoms.clear();
		tAtoms.addAll(eBodyAtoms);
		for (Atom atom : tAtoms) {
			tVariables.clear();
			atom.getVariables(tVariables);
			for (Variable var : tVariables)
				if (mVariables.contains(var)) {
					eBodyAtoms.remove(atom);
					break;
				}
		}

		/*
		 * dealing with equalities of nominal
		 */
		Map<Variable, String> nom2iri = new HashMap<Variable, String>();
		tAtoms.clear();
		tAtoms.addAll(eBodyAtoms);
		for (Atom atom : tAtoms) {
			predicate = atom.getDLPredicate();
			if (predicate instanceof AtomicConcept
					&& predicate.toString().startsWith("<internal:nom#")) {
				nom2iri.put(atom.getArgumentVariable(0),
						getIRI4Nominal(predicate));
				eBodyAtoms.remove(atom);
			}
		}

		Variable first, second;
		Map<Variable, Set<Variable>> equEdges = new HashMap<Variable, Set<Variable>>();
		for (Atom atom : eHeadAtoms) {
			predicate = atom.getDLPredicate();
			if (predicate instanceof Equality) {
				first = atom.getArgumentVariable(0);
				second = atom.getArgumentVariable(1);

				if ((tVariables = equEdges.get(first)) == null)
					equEdges.put(first, (tVariables = new HashSet<Variable>()));
				tVariables.add(second);

				if ((tVariables = equEdges.get(second)) == null)
					equEdges.put(second, (tVariables = new HashSet<Variable>()));
				tVariables.add(first);
			}
		}

		OWLObjectPropertyExpression objExp;
		Set<OWLNamedIndividual> individuals = new HashSet<OWLNamedIndividual>();

		if (equEdges.containsKey(X)) {
			for (Variable var : equEdges.get(X))
				individuals.add(factory.getOWLNamedIndividual(IRI
						.create(nom2iri.get(var))));
			superClasses.add(factory.getOWLObjectOneOf(individuals));
			// TODO: Yujiao - one of cannot be handle by OWL 2 RL
			// search for objectOneOf
		}

		for (Atom atom : eBodyAtoms) {
			predicate = atom.getDLPredicate();
			if (predicate instanceof AtomicRole) {
				first = atom.getArgumentVariable(0);
				second = atom.getArgumentVariable(1);

				objExp = factory.getOWLObjectProperty(IRI
						.create(((AtomicRole) predicate).getIRI()));
				if (eVariables.contains(first)) {
					second = first;
					objExp = factory.getOWLObjectInverseOf(objExp);
				}

				for (Variable var : equEdges.get(second))
					individuals.add(factory.getOWLNamedIndividual(IRI
							.create(nom2iri.get(var))));

				// TODO: Yujiao - nominals add abox assertion!!!
				superClasses.add(factory.getOWLObjectAllValuesFrom(objExp,
						factory.getOWLObjectOneOf(individuals)));
			}
		}

	}

	private String getIRI4Nominal(DLPredicate predicate) {
		return ((AtomicConcept) predicate).getIRI()
				.replace("internal:nom#", "");
	}

	private OWLObjectMaxCardinality getMaxCardinalityExpression(
			AnnotatedEquality equ) {
		OWLObjectPropertyExpression propExp = getObjectPropertyExpression(equ
				.getOnRole());
		OWLClassExpression clsExp = getClassExpression(equ.getToConcept());
		return factory.getOWLObjectMaxCardinality(equ.getCaridnality(),
				propExp, clsExp);
	}

	private OWLObjectPropertyExpression getObjectPropertyExpression(Role role) {
		if (role instanceof AtomicRole)
			return factory.getOWLObjectProperty(IRI.create(((AtomicRole) role)
					.getIRI()));
		return factory.getOWLObjectProperty(
				IRI.create(((InverseRole) role).getInverseOf().getIRI()))
				.getInverseProperty();
	}

	private OWLDataProperty getDataPropertyExpression(Role role) {
		return factory.getOWLDataProperty(IRI.create(((AtomicRole) role)
				.getIRI()));
	}

	private OWLClassExpression getClassExpression(LiteralConcept concept) {
		if (concept instanceof AtomicConcept)
			return factory.getOWLClass(IRI.create(((AtomicConcept) concept)
					.getIRI()));
		return factory.getOWLClass(
				IRI.create(((AtomicNegationConcept) concept)
						.getNegatedAtomicConcept().getIRI()))
				.getComplementNNF();
	}

	private OWLDataRange getDataRange(LiteralDataRange dataRange) {
		if (dataRange instanceof InternalDatatype)
			return factory.getOWLDatatype(IRI
					.create(((InternalDatatype) dataRange).getIRI()));
		if (dataRange instanceof DatatypeRestriction)
			return factory
					.getOWLDatatype(IRI
							.create(((DatatypeRestriction) dataRange)
									.getDatatypeURI()));
		if (dataRange instanceof ConstantEnumeration) {
			ConstantEnumeration e = (ConstantEnumeration) dataRange;
			OWLLiteral[] values = new OWLLiteral[e.getNumberOfConstants()];
			for (int i = 0; i < values.length; ++i) {
				Constant c = e.getConstant(i);
				values[i] = factory.getOWLLiteral(c.getDataValue().toString(),
						factory.getOWLDatatype(IRI.create(c.getDatatypeURI())));
			}
			return factory.getOWLDataOneOf(values);
		}
		System.out.println(dataRange.toString() + "\nstrange data type!!!!");
		return null;
	}

	public void seperateEquality4Clause(Set<Atom> eBodyAtoms,
			Set<Atom> eHeadAtoms, Set<Variable> eVariables) {
		Set<Variable> variables = new HashSet<Variable>();
		DLPredicate predicate;
		for (Atom atom : headAtoms) {
			predicate = atom.getDLPredicate();
			if (predicate instanceof Equality
					|| predicate instanceof AnnotatedEquality) {
				variables.clear();
				atom.getVariables(variables);
				for (Variable variable : variables)
					eVariables.add(variable);
			}
		}
		eVariables.remove(X);

		seperateEquality(bodyAtoms, eBodyAtoms, eVariables);
		seperateEquality(headAtoms, eHeadAtoms, eVariables);
	}

	public void seperateEquality(Set<Atom> noEquality, Set<Atom> inEquality,
			Set<Variable> eVariables) {
		Set<Variable> variables = new HashSet<Variable>();
		Set<Atom> temp = new HashSet<Atom>();
		temp.addAll(noEquality);
		for (Atom atom : temp) {
			variables.clear();
			atom.getVariables(variables);
			for (Variable variable : variables)
				if (eVariables.contains(variable)) {
					noEquality.remove(atom);
					inEquality.add(atom);
					break;
				}
		}
		temp.clear();
	}

	@Override
	public String toString() {
		String ret = "";
		boolean first = true;
		for (OWLClassExpression exp : superClasses)
			if (first) {
				ret = exp.toString();
				first = false;
			} else
				ret += " v " + exp.toString();

		first = true;
		for (OWLClassExpression exp : subClasses)
			if (first) {
				ret += " :- " + exp.toString();
				first = false;
			} else
				ret += " ^ " + exp.toString();

		return ret;
	}
}
