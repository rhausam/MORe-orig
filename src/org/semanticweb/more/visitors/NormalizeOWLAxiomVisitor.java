package org.semanticweb.more.visitors;

import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;

public class NormalizeOWLAxiomVisitor extends AbstractNormalizeOWLAxiomVisitor {

	NormalizeOWLClassExpressionVisitor classExpNormaliser;

	Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
	OWLDataFactory factory;

	private boolean wasAxiomProcessed;

	public NormalizeOWLAxiomVisitor(OWLDataFactory factory) {
		this.factory = factory;

		classExpNormaliser = new NormalizeOWLClassExpressionVisitor(factory);
	}

	public void resetStructures() {
		axioms.clear();
		wasAxiomProcessed = false;
	}

	public Set<OWLAxiom> getNormalizedAxioms() {
		return axioms;
	}

	public boolean wasAxiomProcessed() {
		return wasAxiomProcessed;
	}

	@Override
	public void visit(OWLSubClassOfAxiom ax) {

		wasAxiomProcessed = true;

		boolean wasOneSideNormalized = false;

		// Check if right side is an intersection, or min cardinality
		if (!ax.getSubClass().isAnonymous()) {

			classExpNormaliser.clearExpressions();

			classExpNormaliser.setRightSideNormalization();

			ax.getSuperClass().accept(classExpNormaliser);

			wasOneSideNormalized = (classExpNormaliser
					.getNormalizedExpressions().size() > 0);

			// If there was a normalisation
			for (OWLClassExpression expression : classExpNormaliser
					.getNormalizedExpressions()) {

				axioms.add(factory.getOWLSubClassOfAxiom(ax.getSubClass(),
						expression));
			}
		}

		// Check if left side is an union
		else if (!ax.getSuperClass().isAnonymous()) {

			classExpNormaliser.clearExpressions();

			classExpNormaliser.setLeftSideNormalization();

			ax.getSubClass().accept(classExpNormaliser);

			wasOneSideNormalized = (classExpNormaliser
					.getNormalizedExpressions().size() > 0);

			// If there was a normalisation
			for (OWLClassExpression expression : classExpNormaliser
					.getNormalizedExpressions()) {

				axioms.add(factory.getOWLSubClassOfAxiom(expression,
						ax.getSuperClass()));
			}
		}

		// If intersection or min cardinality
		if (!wasOneSideNormalized) {
			axioms.add(ax);
		} else {
			// System.out.println("Normalising 'OWLSubClassOfAxiom' into "+
			// axioms.size() + " axioms.");
			// System.out.println(axioms);
		}

	}

	@Override
	public void visit(OWLEquivalentClassesAxiom ax) {

		wasAxiomProcessed = true;

		// Split into two axioms and apply visitor

		OWLAxiom aux_ax;

		for (int i = 0; i < ax.getClassExpressionsAsList().size() - 1; i++) {

			for (int j = i + 1; j < ax.getClassExpressionsAsList().size(); j++) {

				aux_ax = factory.getOWLSubClassOfAxiom(ax
						.getClassExpressionsAsList().get(i), ax
						.getClassExpressionsAsList().get(j));

				aux_ax.accept(this);

				aux_ax = factory.getOWLSubClassOfAxiom(ax
						.getClassExpressionsAsList().get(j), ax
						.getClassExpressionsAsList().get(i));

				aux_ax.accept(this);

			}

		}

		// System.out.println("Normalising 'OWLEquivalentClassesAxiom' into "+
		// axioms.size() + " axioms.");
		// System.out.println(axioms);

	}

	@Override
	public void visit(OWLDisjointClassesAxiom ax) {

		wasAxiomProcessed = true;

		// Transform in A intersect B -> bottom
		for (int i = 0; i < ax.getClassExpressionsAsList().size() - 1; i++) {

			for (int j = i + 1; j < ax.getClassExpressionsAsList().size(); j++) {

				axioms.add(factory.getOWLSubClassOfAxiom(factory
						.getOWLObjectIntersectionOf(ax
								.getClassExpressionsAsList().get(i), ax
								.getClassExpressionsAsList().get(j)), factory
						.getOWLNothing()));
			}

		}

		// System.out.println("Normalising 'OWLDisjointClassesAxiom' into "+
		// axioms.size() + " axioms.");
		// System.out.println(axioms);

	}

	public void visit(OWLInverseFunctionalObjectPropertyAxiom ax) {

		wasAxiomProcessed = true;

		axioms.add(factory.getOWLFunctionalObjectPropertyAxiom(factory
				.getOWLObjectInverseOf(ax.getProperty())));

	}

	public void visit(OWLObjectPropertyRangeAxiom ax) {

		wasAxiomProcessed = true;

		axioms.add(factory.getOWLSubClassOfAxiom(
		// factory.getOWLThing(),
		// factory.getOWLObjectAllValuesFrom(
		// ax.getProperty(), ax.getRange())
				factory.getOWLObjectSomeValuesFrom(
						factory.getOWLObjectInverseOf(ax.getProperty()),
						factory.getOWLThing()), ax.getRange()));

	}

	public void visit(OWLDataPropertyRangeAxiom ax) {

		wasAxiomProcessed = true;

		// for now in our tets lets ignore DataPropertyAxioms and also
		// RoleChainAxioms
		System.out.println("an OWLDataPropertyRangeAxiom has been omitted");
		// axioms.add(
		// factory.getOWLSubClassOfAxiom(
		// factory.getOWLThing(),
		// factory.getOWLDataAllValuesFrom(
		// ax.getProperty(), ax.getRange())
		// )
		// );

	}

	public void visit(OWLObjectPropertyDomainAxiom ax) {

		wasAxiomProcessed = true;

		axioms.add(factory.getOWLSubClassOfAxiom(
				factory.getOWLObjectSomeValuesFrom(ax.getProperty(),
						factory.getOWLThing()), ax.getDomain()));

	}

	public void visit(OWLDataPropertyDomainAxiom ax) {

		wasAxiomProcessed = true;

		axioms.add(factory.getOWLSubClassOfAxiom(
				factory.getOWLDataSomeValuesFrom(ax.getProperty(),
						factory.getTopDatatype()), ax.getDomain()));

	}

}
