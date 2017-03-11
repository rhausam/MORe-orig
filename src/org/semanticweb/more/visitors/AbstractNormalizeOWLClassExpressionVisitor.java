package org.semanticweb.more.visitors;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;

public abstract class AbstractNormalizeOWLClassExpressionVisitor implements
		OWLClassExpressionVisitor {

	// In principle we are only interested in this cases
	public abstract void visit(OWLObjectIntersectionOf arg0);

	public abstract void visit(OWLObjectMinCardinality arg0);

	public abstract void visit(OWLDataMinCardinality arg0);

	public abstract void visit(OWLObjectUnionOf arg0);

	public void visit(OWLClass arg0) {
	}

	public void visit(OWLObjectSomeValuesFrom arg0) {

	}

	public void visit(OWLDataSomeValuesFrom arg0) {

	}

	public void visit(OWLObjectComplementOf arg0) {

	}

	public void visit(OWLObjectAllValuesFrom arg0) {

	}

	public void visit(OWLObjectHasValue arg0) {

	}

	public void visit(OWLObjectExactCardinality arg0) {
	}

	public void visit(OWLObjectMaxCardinality arg0) {
	}

	public void visit(OWLObjectHasSelf arg0) {
	}

	public void visit(OWLObjectOneOf arg0) {
	}

	public void visit(OWLDataAllValuesFrom arg0) {
	}

	public void visit(OWLDataHasValue arg0) {
	}

	public void visit(OWLDataExactCardinality arg0) {

	}

	public void visit(OWLDataMaxCardinality arg0) {

	}

}
