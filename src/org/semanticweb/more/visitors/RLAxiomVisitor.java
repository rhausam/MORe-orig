package org.semanticweb.more.visitors;

import java.util.Iterator;

import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiomVisitor;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLClassExpressionVisitor;
import org.semanticweb.owlapi.model.OWLDataAllValuesFrom;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataIntersectionOf;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLDatatypeDefinitionAxiom;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLHasKeyAxiom;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.SWRLRule;

public class RLAxiomVisitor implements OWLAxiomVisitor {

	// this class checks whether an axiom is in the OWL 2 RL profile
	private boolean isRL;

	public boolean isRL() {
		return isRL;
	}

	/*
	 * Class Axioms
	 */

	@Override
	public void visit(OWLSubClassOfAxiom axiom) {
		isRL = isValidSubClassExpression(axiom.getSubClass())
				&& isValidSuperClassExpression(axiom.getSuperClass());
	}

	@Override
	public void visit(OWLEquivalentClassesAxiom axiom) {
		isRL = true;
		Iterator<OWLClassExpression> it = axiom.getClassExpressions()
				.iterator();
		while (isRL && it.hasNext()) {
			OWLClassExpression c = it.next();
			isRL = isValidSubClassExpression(c)
					&& isValidSuperClassExpression(c);
		}
	}

	@Override
	public void visit(OWLDisjointClassesAxiom axiom) {
		isRL = true;
		Iterator<OWLClassExpression> it = axiom.getClassExpressions()
				.iterator();
		while (isRL && it.hasNext())
			isRL = isValidSubClassExpression(it.next());
	}

	@Override
	public void visit(OWLDisjointUnionAxiom axiom) {
		isRL = false;
	}

	/*
	 * Object Property Axioms
	 */

	@Override
	public void visit(OWLSubObjectPropertyOfAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLSubPropertyChainOfAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLInverseObjectPropertiesAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLObjectPropertyDomainAxiom axiom) {
		isRL = isValidSuperClassExpression(axiom.getDomain());
	}

	@Override
	public void visit(OWLObjectPropertyRangeAxiom axiom) {
		isRL = isValidSuperClassExpression(axiom.getRange());
	}

	@Override
	public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
		isRL = true;
	}

	/*
	 * Data Property Axioms
	 */

	@Override
	public void visit(OWLSubDataPropertyOfAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLDisjointDataPropertiesAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLDataPropertyDomainAxiom axiom) {
		isRL = isValidSuperClassExpression(axiom.getDomain());
	}

	@Override
	public void visit(OWLDataPropertyRangeAxiom axiom) {
		isRL = axiom.getRange().isDatatype()
				|| axiom.getRange() instanceof OWLDataIntersectionOf;
	}

	@Override
	public void visit(OWLFunctionalDataPropertyAxiom axiom) {
		isRL = true;
	}

	/*
	 * Other Axioms
	 */

	@Override
	public void visit(OWLHasKeyAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLDeclarationAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLDatatypeDefinitionAxiom axiom) {
		isRL = true;
	}

	// should we ignore this??
	@Override
	public void visit(SWRLRule axiom) {
		isRL = true;// ??
	}

	/*
	 * ASSERTION/ANNOTATION AXIOMS (IGNORED AXIOMS)
	 */

	@Override
	public void visit(OWLAnnotationAssertionAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLSubAnnotationPropertyOfAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLAnnotationPropertyDomainAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLAnnotationPropertyRangeAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLClassAssertionAxiom axiom) {
		isRL = isValidSuperClassExpression(axiom.getClassExpression());
	}

	@Override
	public void visit(OWLObjectPropertyAssertionAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLDataPropertyAssertionAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLSameIndividualAxiom axiom) {
		isRL = true;
	}

	@Override
	public void visit(OWLDifferentIndividualsAxiom axiom) {
		isRL = true;
	}

	private boolean isValidSubClassExpression(OWLClassExpression ce) {
		RLSubClassExpressionVisitor visitor = new RLSubClassExpressionVisitor();
		return visitor.isValidSubClassExpression(ce);
	}

	private boolean isValidSuperClassExpression(OWLClassExpression ce) {
		RLSuperClassExpressionVisitor visitor = new RLSuperClassExpressionVisitor();
		return visitor.isValidSuperClassExpression(ce);
	}

	// ------------------------

	protected class RLSubClassExpressionVisitor implements
			OWLClassExpressionVisitor {

		boolean is;

		public boolean isValidSubClassExpression(OWLClassExpression ce) {
			ce.accept(this);
			return is;
		}

		@Override
		public void visit(OWLClass ce) {
			is = !ce.isOWLThing();
		}

		@Override
		public void visit(OWLObjectIntersectionOf ce) {
			is = true;
			Iterator<OWLClassExpression> it = ce.getOperands().iterator();
			while (is && it.hasNext())
				isValidSubClassExpression(it.next());
		}

		@Override
		public void visit(OWLObjectUnionOf ce) {
			is = true;
			Iterator<OWLClassExpression> it = ce.getOperands().iterator();
			while (is && it.hasNext())
				isValidSubClassExpression(it.next());
		}

		@Override
		public void visit(OWLObjectSomeValuesFrom ce) {
			isValidSubClassExpression(ce.getFiller());
			is = is || ce.getFiller().isOWLThing();
		}

		@Override
		public void visit(OWLObjectHasValue ce) {
			is = true;
		}

		@Override
		public void visit(OWLObjectOneOf ce) {
			is = true;
		}

		@Override
		public void visit(OWLDataHasValue ce) {
			is = true;
		}

		@Override
		public void visit(OWLObjectComplementOf ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectAllValuesFrom ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectMinCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectExactCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectMaxCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectHasSelf ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataSomeValuesFrom ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataAllValuesFrom ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataMinCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataExactCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataMaxCardinality ce) {
			is = false;
		}
	}

	private class RLSuperClassExpressionVisitor implements
			OWLClassExpressionVisitor {

		boolean is;

		public boolean isValidSuperClassExpression(OWLClassExpression ce) {
			ce.accept(this);
			return is;
		}

		@Override
		public void visit(OWLClass ce) {
			is = !ce.isOWLThing();
		}

		@Override
		public void visit(OWLObjectIntersectionOf ce) {
			is = true;
			Iterator<OWLClassExpression> it = ce.getOperands().iterator();
			while (is && it.hasNext())
				isValidSuperClassExpression(it.next());
		}

		@Override
		public void visit(OWLObjectUnionOf ce) {
			is = true;
			Iterator<OWLClassExpression> it = ce.getOperands().iterator();
			while (is && it.hasNext())
				isValidSuperClassExpression(it.next());
		}

		@Override
		public void visit(OWLObjectComplementOf ce) {
			is = isValidSubClassExpression(ce.getOperand());
		}

		@Override
		public void visit(OWLObjectAllValuesFrom ce) {
			isValidSuperClassExpression(ce.getFiller());
		}

		@Override
		public void visit(OWLObjectHasValue ce) {
			is = true;
		}

		@Override
		public void visit(OWLObjectMaxCardinality ce) {
			is = (ce.getCardinality() == 0 || ce.getCardinality() == 1)
					&& (isValidSubClassExpression(ce.getFiller()) || ce
							.getFiller().isOWLThing());
		}

		@Override
		public void visit(OWLDataAllValuesFrom ce) {
			is = true;
		}

		@Override
		public void visit(OWLDataMaxCardinality ce) {
			is = (ce.getCardinality() == 0 || ce.getCardinality() == 1)
					&& (ce.getFiller() instanceof OWLDataIntersectionOf || ce
							.getFiller().isDatatype());
		}

		@Override
		public void visit(OWLObjectSomeValuesFrom ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectMinCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectExactCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectHasSelf ce) {
			is = false;
		}

		@Override
		public void visit(OWLObjectOneOf ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataSomeValuesFrom ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataHasValue ce) {
			is = true;
		}

		@Override
		public void visit(OWLDataMinCardinality ce) {
			is = false;
		}

		@Override
		public void visit(OWLDataExactCardinality ce) {
			is = false;
		}
	}
}