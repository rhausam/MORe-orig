package org.semanticweb.more.visitors;

import org.semanticweb.owlapi.model.OWLDataFactory;

import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLClassExpression;

import java.util.Set;
import java.util.HashSet;

public class NormalizeOWLClassExpressionVisitor extends
		AbstractNormalizeOWLClassExpressionVisitor {

	OWLDataFactory factory;
	Set<OWLClassExpression> expressions = new HashSet<OWLClassExpression>();

	boolean rightSide = false;

	boolean wasNormalized = false;

	public void clearExpressions() {
		expressions.clear();
	}

	public Set<OWLClassExpression> getNormalizedExpressions() {
		return expressions;
	}

	public NormalizeOWLClassExpressionVisitor(OWLDataFactory factory) {
		this.factory = factory;

	}

	public void setRightSideNormalization() {
		rightSide = true;
	}

	public void setLeftSideNormalization() {
		rightSide = false;
	}

	public boolean isRightSideNormalization() {
		return rightSide;
	}

	public boolean isLeftSideNormalization() {
		return !rightSide;
	}

	@Override
	public void visit(OWLObjectIntersectionOf expressionIntersection) {

		if (isRightSideNormalization()) {

			for (OWLClassExpression expression : expressionIntersection
					.getOperands()) {

				wasNormalized = false;

				expression.accept(this);

				if (!wasNormalized) {
					expressions.add(expression);
				}

			}
		}
	}

	@Override
	public void visit(OWLObjectUnionOf expressionUnion) {

		if (isLeftSideNormalization()) {

			for (OWLClassExpression expression : expressionUnion.getOperands()) {

				wasNormalized = false;

				expression.accept(this);

				if (!wasNormalized) {
					expressions.add(expression);
				}

			}
		}
	}

	@Override
	public void visit(OWLObjectMinCardinality minExpression) {

		if (minExpression.getCardinality() == 1) {
			expressions.add(factory.getOWLObjectSomeValuesFrom(
					minExpression.getProperty(), minExpression.getFiller()));
			wasNormalized = true;
		}

	}

	@Override
	public void visit(OWLDataMinCardinality minExpression) {
		if (minExpression.getCardinality() == 1) {
			expressions.add(factory.getOWLDataSomeValuesFrom(
					minExpression.getProperty(), minExpression.getFiller()));
			wasNormalized = true;
		}

	}

}
