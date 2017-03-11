package org.semanticweb.more.RLrewriting;

import java.util.Set;

import org.semanticweb.owlapi.model.*;

public class RLChecker {

	public boolean check(OWLAxiom axiom) {
		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom subAxiom = (OWLSubClassOfAxiom) axiom;
			return checkSub(subAxiom.getSubClass())
					&& checkSuper(subAxiom.getSuperClass());
		}

		if (axiom instanceof OWLEquivalentClassesAxiom)
			return checkEquiv(((OWLEquivalentClassesAxiom) axiom)
					.getClassExpressions());

		if (axiom instanceof OWLDisjointClassesAxiom)
			return checkSub(((OWLDisjointClassesAxiom) axiom)
					.getClassExpressions());

		if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom domAxiom = (OWLObjectPropertyDomainAxiom) axiom;
			return check(domAxiom.getProperty())
					&& checkSuper(domAxiom.getDomain());
		}

		if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom ranAxiom = (OWLObjectPropertyRangeAxiom) axiom;
			return check(ranAxiom.getProperty())
					&& checkSuper(ranAxiom.getRange());
		}

		if (axiom instanceof OWLDataPropertyDomainAxiom) {
			OWLDataPropertyDomainAxiom domAxiom = (OWLDataPropertyDomainAxiom) axiom;
			return check(domAxiom.getProperty())
					&& checkSuper(domAxiom.getDomain());
		}

		if (axiom instanceof OWLReflexiveObjectPropertyAxiom)
			return false;

		if (axiom instanceof OWLHasKeyAxiom)
			return checkSub(((OWLHasKeyAxiom) axiom).getClassExpression());

		return true;
	}

	private boolean checkEquiv(OWLClassExpression exp) {
		if (exp instanceof OWLClass)
			return !exp.isTopEntity();

		if (exp instanceof OWLObjectIntersectionOf)
			return checkEquiv(((OWLObjectIntersectionOf) exp).getOperands());

		if (exp instanceof OWLObjectHasValue)
			return check(((OWLObjectHasValue) exp).getProperty());

		if (exp instanceof OWLDataHasValue)
			return check(((OWLDataHasValue) exp).getProperty());

		return false;
	}

	private boolean checkEquiv(Set<OWLClassExpression> operands) {
		for (OWLClassExpression exp : operands)
			if (!checkEquiv(exp))
				return false;
		return true;
	}

	public boolean checkSub(OWLClassExpression exp) {
		if (exp instanceof OWLClass)
			return !exp.isTopEntity();

		if (exp instanceof OWLObjectIntersectionOf)
			return checkSub(((OWLObjectIntersectionOf) exp).getOperands());

		if (exp instanceof OWLObjectUnionOf)
			return checkSub(((OWLObjectUnionOf) exp).getOperands());

		if (exp instanceof OWLObjectOneOf)
			return true;

		if (exp instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom someValueExp = (OWLObjectSomeValuesFrom) exp;
			return check(someValueExp.getProperty())
					&& (someValueExp.getFiller().isTopEntity() || checkSub(someValueExp
							.getFiller()));
		}

		if (exp instanceof OWLObjectHasValue)
			return check(((OWLObjectHasValue) exp).getProperty());

		if (exp instanceof OWLDataSomeValuesFrom) {
			OWLDataSomeValuesFrom someValueExp = (OWLDataSomeValuesFrom) exp;
			return check(someValueExp.getProperty())
					&& check(someValueExp.getFiller());
		}

		if (exp instanceof OWLDataHasValue)
			return check(((OWLDataHasValue) exp).getProperty());

		return false;
	}

	public boolean checkSuper(OWLClassExpression exp) {
		if (exp instanceof OWLClass)
			return !exp.isTopEntity();

		if (exp instanceof OWLObjectIntersectionOf)
			return checkSuper(((OWLObjectIntersectionOf) exp).getOperands());

		if (exp instanceof OWLObjectComplementOf)
			return checkSub(((OWLObjectComplementOf) exp).getComplementNNF());

		if (exp instanceof OWLObjectAllValuesFrom) {
			OWLObjectAllValuesFrom allValueExp = (OWLObjectAllValuesFrom) exp;
			return check(allValueExp.getProperty())
					&& (allValueExp.getFiller().isTopEntity() || checkSuper(allValueExp
							.getFiller()));
		}

		if (exp instanceof OWLObjectHasValue)
			return check(((OWLObjectHasValue) exp).getProperty());

		if (exp instanceof OWLObjectMaxCardinality) {
			OWLObjectMaxCardinality maxCardExp = (OWLObjectMaxCardinality) exp;
			if (maxCardExp.getCardinality() > 1)
				return false;
			return check(maxCardExp.getProperty())
					&& (!maxCardExp.isQualified()
							|| maxCardExp.getFiller().isTopEntity() || checkSub(maxCardExp
								.getFiller()));
		}

		if (exp instanceof OWLDataAllValuesFrom) {
			OWLDataAllValuesFrom allValueExp = (OWLDataAllValuesFrom) exp;
			return check(allValueExp.getProperty())
					&& check(allValueExp.getFiller());
		}

		if (exp instanceof OWLDataHasValue)
			return check(((OWLDataHasValue) exp).getProperty());

		if (exp instanceof OWLDataMaxCardinality) {
			OWLDataMaxCardinality maxCardExp = (OWLDataMaxCardinality) exp;
			if (maxCardExp.getCardinality() > 1)
				return false;
			return check(maxCardExp.getProperty())
					&& check(maxCardExp.getFiller());
		}

		return false;
	}

	private boolean checkSuper(Set<OWLClassExpression> operands) {
		for (OWLClassExpression exp : operands)
			if (!checkSuper(exp))
				return false;
		return true;
	}

	private boolean checkSub(Set<OWLClassExpression> operands) {
		for (OWLClassExpression exp : operands)
			if (!checkSub(exp))
				return false;
		return true;
	}

	private boolean check(OWLDataRange filler) {
		if (filler instanceof OWLDatatype)
			return true;
		if (filler instanceof OWLDataIntersectionOf)
			return check(((OWLDataIntersectionOf) filler).getOperands());
		return false;
	}

	private boolean check(Set<OWLDataRange> operands) {
		for (OWLDataRange type : operands)
			if (!check(type))
				return false;
		return true;
	}

	private boolean check(OWLDataPropertyExpression property) {
		return property instanceof OWLDataProperty;
	}

	private boolean check(OWLObjectPropertyExpression property) {
		return property.getSimplified() instanceof OWLObjectProperty
				|| property.getInverseProperty().getSimplified() instanceof OWLObjectProperty;
	}

}
