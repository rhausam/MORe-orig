package org.semanticweb.more;

import java.util.Set;
import java.util.List;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Iterator;

import org.semanticweb.owlapi.model.*;

/**
 * Based on the codes from Ernesto Jiménez, this axiom visitor checks whether an
 * axiom is bottom-local wrt a given external signature and, if the answer is
 * negative, provides several sets of symbols that could be removed from this
 * external signature in order to make it local (if such sets exist)
 */

public class BottomLocalityChecker implements OWLAxiomVisitor {

	private boolean isLocal;
	private boolean canMakeLocal;
	private List<Set<OWLEntity>> solutions;

	private Set<OWLEntity> externalSignature;

	private BottomChecker negativeVisitor;
	private TopChecker positiveVisitor;

	private boolean returnSolutions;

	public BottomLocalityChecker(boolean returnSolutions) {
		this.returnSolutions = returnSolutions;
		positiveVisitor = new TopChecker();
		negativeVisitor = new BottomChecker();
	}

	public void setExternalSignature(Set<OWLEntity> signature) {
		externalSignature = signature;
	}

	public LocalityInfo isLocalAxiom(OWLAxiom axiom, Set<OWLEntity> extSignature) {
		externalSignature = extSignature;
		axiom.accept(this);
		return new LocalityInfo(isLocal, canMakeLocal, solutions);
		// all three variables canMakeLocal, isLocal and solutions are updated
		// every time an axiom is visited
	}

	protected LocalityInfo isBottomClass(OWLClassExpression exp) {
		exp.accept(negativeVisitor);
		return negativeVisitor.info();
	}

	protected LocalityInfo isTopClass(OWLClassExpression exp) {
		exp.accept(positiveVisitor);
		return positiveVisitor.info();
	}

	/*
	 * ------------------------------------------------ CLASS AXIOMS
	 * -------------------------------------------------
	 */

	public void visit(OWLSubClassOfAxiom axiom) {
		// An OWLSubClassOfAxiom is bot-local if the subclass is locally bottom
		// or the superclass is locally top
		if (returnSolutions) {
			LocalityInfo bottomInfo = isBottomClass(axiom.getSubClass());
			LocalityInfo topInfo = isTopClass(axiom.getSuperClass());
			isLocal = bottomInfo.is() || topInfo.is();
			if (isLocal) {
				canMakeLocal = true;
				solutions = new LinkedList<Set<OWLEntity>>();
			} else {
				canMakeLocal = false;
				solutions = new LinkedList<Set<OWLEntity>>();
				if (bottomInfo.canMake()) {
					canMakeLocal = true;
					solutions.addAll(bottomInfo.getSolutions());
				}
				if (topInfo.canMake()) {
					canMakeLocal = true;
					solutions.addAll(topInfo.getSolutions());
				}
			}
		} else {
			LocalityInfo bottomInfo = isBottomClass(axiom.getSubClass());
			LocalityInfo topInfo = isTopClass(axiom.getSuperClass());
			isLocal = bottomInfo.is() || topInfo.is();
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLDisjointClassesAxiom axiom) {
		// An OWLDisjointClassesAxiom is bot-local if at most one of the
		// involved class expressions is not locally negative.";
		if (returnSolutions) {
			List<OWLClassExpression> classExps = axiom
					.getClassExpressionsAsList();
			if (returnSolutions) {
				List<List<Set<OWLEntity>>> sols = new LinkedList<List<Set<OWLEntity>>>();

				ListProcessor listProc = new ListProcessor();
				int nAlreadyBott = 0;
				int nCanBeBott = 0;
				int nExps = classExps.size();
				LocalityInfo locInfo;
				for (OWLClassExpression exp : classExps) {
					locInfo = isBottomClass(exp);
					if (locInfo.is()) {
						nCanBeBott++;
						nAlreadyBott++;
					} else {
						if (locInfo.canMake()) {
							nCanBeBott++;
							sols.add(locInfo.getSolutions());
						}
					}
				}

				solutions = new LinkedList<Set<OWLEntity>>();

				if (nAlreadyBott > nExps - 2) {
					isLocal = true;
					canMakeLocal = true;
				} else {
					isLocal = false;
					if (nCanBeBott < nExps - 1) {
						canMakeLocal = false;
					} else {
						if (nCanBeBott < nExps) {
							canMakeLocal = true;
							solutions = listProc.getAllCombinations(sols, true); // true
																					// because
																					// we
																					// want
																					// solutions
																					// containing
																					// one
																					// of
																					// the
																					// solutions
																					// for
																					// each
																					// disjunct
						} else {
							canMakeLocal = true;
							solutions = listProc
									.getAllCombinations(sols, false); // false
																		// because
																		// we
																		// want
																		// solutions
																		// containing
																		// one
																		// of
																		// the
																		// solutions
																		// for
																		// all
																		// but
																		// one
																		// of
																		// the
																		// disjuncts
						}
					}
				}
			} else {
				int nAlreadyBott = 0;
				int nExps = classExps.size();
				LocalityInfo locInfo;
				for (OWLClassExpression exp : classExps) {
					locInfo = isBottomClass(exp);
					if (locInfo.is()) {
						nAlreadyBott++;
					}
				}
				if (nAlreadyBott > nExps - 2) {
					isLocal = true;
					canMakeLocal = true;
				} else {
					isLocal = false;
					canMakeLocal = false;
				}
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		} else {
			List<OWLClassExpression> classExps = axiom
					.getClassExpressionsAsList();
			if (returnSolutions) {
				List<List<Set<OWLEntity>>> sols = new LinkedList<List<Set<OWLEntity>>>();

				ListProcessor listProc = new ListProcessor();
				int nAlreadyBott = 0;
				int nCanBeBott = 0;
				int nExps = classExps.size();
				LocalityInfo locInfo;
				for (OWLClassExpression exp : classExps) {
					locInfo = isBottomClass(exp);
					if (locInfo.is()) {
						nCanBeBott++;
						nAlreadyBott++;
					} else {
						if (locInfo.canMake()) {
							nCanBeBott++;
							sols.add(locInfo.getSolutions());
						}
					}
				}

				solutions = new LinkedList<Set<OWLEntity>>();

				if (nAlreadyBott > nExps - 2) {
					isLocal = true;
					canMakeLocal = true;
				} else {
					isLocal = false;
					if (nCanBeBott < nExps - 1) {
						canMakeLocal = false;
					} else {
						if (nCanBeBott < nExps) {
							canMakeLocal = true;
							solutions = listProc.getAllCombinations(sols, true); // true
																					// because
																					// we
																					// want
																					// solutions
																					// containing
																					// one
																					// of
																					// the
																					// solutions
																					// for
																					// each
																					// disjunct
						} else {
							canMakeLocal = true;
							solutions = listProc
									.getAllCombinations(sols, false); // false
																		// because
																		// we
																		// want
																		// solutions
																		// containing
																		// one
																		// of
																		// the
																		// solutions
																		// for
																		// all
																		// but
																		// one
																		// of
																		// the
																		// disjuncts
						}
					}
				}
			} else {
				int nAlreadyBott = 0;
				int nExps = classExps.size();
				LocalityInfo locInfo;
				for (OWLClassExpression exp : classExps) {
					locInfo = isBottomClass(exp);
					if (locInfo.is()) {
						nAlreadyBott++;
					}
				}
				if (nAlreadyBott > nExps - 2) {
					isLocal = true;
					canMakeLocal = true;
				} else {
					isLocal = false;
					canMakeLocal = false;
				}
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}
	}

	public void visit(OWLEquivalentClassesAxiom axiom) {
		// An OWLEquivalentClassesAxiom is local if all the classes asserted to
		// be equivalent are locally positive or locally negative - all the same
		if (returnSolutions) {
			ListProcessor listProc = new ListProcessor();
			LocalityInfo posInfo;
			LocalityInfo negInfo;

			boolean atLeastOneNotBottom = false;
			boolean atLeastOneNotTop = false;
			boolean cantMakeAllBottom = false;
			boolean cantMakeAllTop = false;
			List<List<Set<OWLEntity>>> solsForBottom = new LinkedList<List<Set<OWLEntity>>>();
			List<List<Set<OWLEntity>>> solsForTop = new LinkedList<List<Set<OWLEntity>>>();

			for (OWLClassExpression exp : axiom.getClassExpressions()) {
				if (!cantMakeAllBottom) {
					isBottomClass(exp);
					negInfo = negativeVisitor.info();
					if (!negInfo.is()) {
						atLeastOneNotBottom = true;
						if (negInfo.canMake()) {
							solsForBottom.add(negInfo.getSolutions());
						} else
							cantMakeAllBottom = true;
					}
				}
				if (!cantMakeAllTop) {
					isTopClass(exp);
					posInfo = positiveVisitor.info();
					if (!posInfo.is()) {
						atLeastOneNotTop = true;
						if (posInfo.canMake()) {
							solsForTop.add(posInfo.getSolutions());
						} else
							cantMakeAllTop = true;
					}
				}
			}
			isLocal = !(atLeastOneNotBottom && atLeastOneNotTop);
			canMakeLocal = !(cantMakeAllBottom && cantMakeAllTop);
			solutions = new LinkedList<Set<OWLEntity>>();
			if (canMakeLocal && !isLocal) {
				if (!cantMakeAllBottom) {
					solutions.addAll(listProc.getAllCombinations(solsForBottom,
							true));
				}
				if (!cantMakeAllTop) {
					solutions.addAll(listProc.getAllCombinations(solsForTop,
							true));
				}
			}
		} else {
			boolean atLeastOneNotBottom = false;
			boolean atLeastOneNotTop = false;

			for (OWLClassExpression exp : axiom.getClassExpressions()) {
				if (!atLeastOneNotBottom) {
					isBottomClass(exp);
					if (!negativeVisitor.info().is()) {
						atLeastOneNotBottom = true;
					}
				}
				if (!atLeastOneNotTop) {
					isTopClass(exp);
					if (!positiveVisitor.info().is()) {
						atLeastOneNotTop = true;
					}
				}
			}
			isLocal = !(atLeastOneNotBottom && atLeastOneNotTop);
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLDisjointUnionAxiom axiom) {
		// An OWLDisjointUnionAxiom is bot-local if the defined class and all
		// the disjunct are locally negative
		if (returnSolutions) {
			LocalityInfo locInfo = isBottomClass(axiom.getOWLClass());
			isLocal = locInfo.is();
			canMakeLocal = locInfo.canMake();
			List<List<Set<OWLEntity>>> solsForBottom = new LinkedList<List<Set<OWLEntity>>>();
			solsForBottom.add(locInfo.getSolutions());
			for (OWLClassExpression classExp : axiom.getClassExpressions()) {
				locInfo = isBottomClass(classExp);
				isLocal = isLocal && locInfo.is();
				canMakeLocal = canMakeLocal && locInfo.canMake();
				solsForBottom.add(locInfo.getSolutions());
			}
			if (isLocal || !canMakeLocal) {
				solutions = new LinkedList<Set<OWLEntity>>();
			} else {
				ListProcessor listProc = new ListProcessor();
				solutions = listProc.getAllCombinations(solsForBottom, true);
			}
		} else {
			isLocal = isBottomClass(axiom.getOWLClass()).is();
			for (OWLClassExpression classExp : axiom.getClassExpressions()) {
				isLocal = isLocal && isBottomClass(classExp).is();
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	// /END CLASS AXIOMS

	/*
	 * ----------------------------------------- PROPERTY AXIOMS
	 * -----------------------------------------
	 */

	public void visit(OWLSubObjectPropertyOfAxiom axiom) {
		// An OWLSubObjectPropertyOfAxiom is bot-local iff the subproperty does
		// not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getSubProperty().getNamedProperty();// whether
																				// the
																				// property
																				// is
																				// anonymous
																				// or
																				// not,
																				// to
																				// make
																				// it
																				// bottom
																				// it
																				// is
																				// enough
																				// to
																				// make
																				// bottom
																				// the
																				// named
																				// proprety
																				// used
																				// to
																				// construct
																				// it
			solutions = new LinkedList<Set<OWLEntity>>();
			canMakeLocal = true;
			if (!externalSignature.contains(prop)) {
				isLocal = true;
			} else {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			if (!externalSignature.contains(axiom.getSubProperty()
					.getNamedProperty())) {
				isLocal = true;
			} else {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLSubDataPropertyOfAxiom axiom) {
		// An OWLSubDataPropertyOfAxiom is bot-local iff the subproperty does
		// not belong to the external signature
		if (returnSolutions) {
			OWLDataProperty prop = axiom.getSubProperty().asOWLDataProperty();
			solutions = new LinkedList<Set<OWLEntity>>();
			canMakeLocal = true;
			if (!externalSignature.contains(prop)) {
				isLocal = true;
			} else {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			if (!externalSignature.contains(axiom.getSubProperty()
					.asOWLDataProperty())) {
				isLocal = true;
			} else {
				isLocal = false;
			}
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
		// An OWLEquivalentObjectPropertiesAxiom is bot-local if only properties
		// outside the external signature are involved
		if (returnSolutions) {
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
			OWLObjectProperty aux;
			for (OWLObjectPropertyExpression objPropExp : axiom.getProperties()) {
				aux = objPropExp.getNamedProperty();
				if (externalSignature.contains(aux)) {
					isLocal = false;
					auxSet.add(aux);
				}
			}
			solutions.add(auxSet);
		} else {
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
			OWLObjectProperty aux;
			for (OWLObjectPropertyExpression objPropExp : axiom.getProperties()) {
				aux = objPropExp.getNamedProperty();
				if (externalSignature.contains(aux)) {
					isLocal = false;
					auxSet.add(aux);
				}
			}
			solutions.add(auxSet);
		}
	}

	public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
		// An OWLEquivalentDataPropertiesAxiom is bot-local if only properties
		// outside the external signature are involved
		if (returnSolutions) {
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
			OWLDataProperty aux;
			for (OWLDataPropertyExpression dataPropExp : axiom.getProperties()) {
				aux = dataPropExp.asOWLDataProperty();
				if (externalSignature.contains(aux)) {
					isLocal = false;
					auxSet.add(aux);
				}
			}
			solutions.add(auxSet);
		} else {
			isLocal = true;
			OWLDataProperty aux;
			for (OWLDataPropertyExpression dataPropExp : axiom.getProperties()) {
				aux = dataPropExp.asOWLDataProperty();
				if (externalSignature.contains(aux)) {
					isLocal = false;
				}
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLDisjointDataPropertiesAxiom axiom) {
		// An OWLDisjointDataPropertiesAxiom is bot-local if at most one of the
		// involved properties is not locally negative.";
		if (returnSolutions) {
			Set<OWLDataProperty> externalProps = new HashSet<OWLDataProperty>();
			for (OWLDataPropertyExpression prop : axiom.getProperties()) {
				if (externalSignature.contains(prop.asOWLDataProperty())) {
					externalProps.add(prop.asOWLDataProperty());
				}
			}

			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();

			if (externalProps.size() > 1) {
				isLocal = false;
				Set<OWLEntity> auxSet;
				for (OWLDataProperty prop : externalProps) {
					auxSet = new HashSet<OWLEntity>();
					auxSet.addAll(externalProps);
					auxSet.remove(prop);
					solutions.add(auxSet);
				}
			}
		} else {
			Set<OWLDataProperty> externalProps = new HashSet<OWLDataProperty>();
			for (OWLDataPropertyExpression prop : axiom.getProperties()) {
				if (externalSignature.contains(prop.asOWLDataProperty())) {
					externalProps.add(prop.asOWLDataProperty());
				}
			}
			isLocal = true;
			if (externalProps.size() > 1) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
		// An OWLDisjointDataPropertiesAxiom is local if at most one of the
		// involved properties is not locally negative.";
		if (returnSolutions) {
			Set<OWLObjectProperty> externalProps = new HashSet<OWLObjectProperty>();
			for (OWLObjectPropertyExpression prop : axiom.getProperties()) {
				if (externalSignature.contains(prop.getNamedProperty())) {
					externalProps.add(prop.getNamedProperty());
				}
			}

			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();

			if (externalProps.size() > 1) {
				isLocal = false;
				Set<OWLEntity> auxSet;
				for (OWLObjectProperty prop : externalProps) {
					auxSet = new HashSet<OWLEntity>();
					auxSet.addAll(externalProps);
					auxSet.remove(prop); // solutions are removing all
											// properties but one from the
											// harlessSignature
					solutions.add(auxSet);
				}
			}
		} else {
			Set<OWLObjectProperty> externalProps = new HashSet<OWLObjectProperty>();
			for (OWLObjectPropertyExpression prop : axiom.getProperties()) {
				if (externalSignature.contains(prop.getNamedProperty())) {
					externalProps.add(prop.getNamedProperty());
				}
			}
			isLocal = true;
			if (externalProps.size() > 1) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLFunctionalDataPropertyAxiom axiom) {
		// An OWLFunctionalDataPropertyAxiom axiom is bot-local iff property
		// does not belong to the external signature
		if (returnSolutions) {
			OWLDataProperty prop = axiom.getProperty().asOWLDataProperty();
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			OWLDataProperty prop = axiom.getProperty().asOWLDataProperty();
			isLocal = true;
			if (externalSignature.contains(prop)) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
		// An OWLFunctionalObjectPropertyAxiom axiom is bot-local iff property
		// does not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			isLocal = true;
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = true;
			if (externalSignature.contains(axiom.getProperty()
					.getNamedProperty())) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
		// An OWLInverseFunctionalObjectPropertyAxiom axiom is bot-local iff
		// property does not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = true;
			if (externalSignature.contains(axiom.getProperty()
					.getNamedProperty())) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLInverseObjectPropertiesAxiom axiom) {
		// An OWLInverseObjectPropertiesAxiom axiom is bot-local iff both
		// involved properties do not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop1 = axiom.getFirstProperty()
					.getNamedProperty();
			OWLObjectProperty prop2 = axiom.getSecondProperty()
					.getNamedProperty();

			boolean b1 = externalSignature.contains(prop1);
			boolean b2 = externalSignature.contains(prop2);

			isLocal = !(b1 || b2);
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();

			if (!isLocal) {
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				if (b1) {
					aux.add(prop1);
				}
				if (b2) {
					aux.add(prop2);
				}
				solutions.add(aux);
			}
		} else {
			boolean b1 = externalSignature.contains(axiom.getFirstProperty()
					.getNamedProperty());
			boolean b2 = externalSignature.contains(axiom.getSecondProperty()
					.getNamedProperty());

			isLocal = !(b1 || b2);
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
		// An OWLIrreflexiveObjectPropertyAxiom axiom is bottom-local iff
		// property does not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = true;
			if (externalSignature.contains(axiom.getProperty()
					.getNamedProperty())) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
		// An OWLAsymmetricObjectPropertyAxiom axiom is bot-local iff property
		// does not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = true;
			if (externalSignature.contains(axiom.getProperty()
					.getNamedProperty())) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
		// An OWLSymmetricObjectPropertyAxiom axiom is bot-local iff property
		// does not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = true;
			if (externalSignature.contains(axiom.getProperty()
					.getNamedProperty())) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
		// An OWLSymmetricObjectPropertyAxiom axiom is bot-local iff property
		// does not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = true;
			if (externalSignature.contains(axiom.getProperty()
					.getNamedProperty())) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
		// An OWLFunctionalObjectPropertyAxiom axiom is bot-local iff property
		// does not belong to the external signature
		if (returnSolutions) {
			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			isLocal = true;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (externalSignature.contains(prop)) {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = true;
			if (externalSignature.contains(axiom.getProperty()
					.getNamedProperty())) {
				isLocal = false;
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLObjectPropertyDomainAxiom axiom) {
		// An OWLObjectPropertyDomainAxiom is bot-local iff the property does
		// not belong to the external signature or the domain is locally top
		if (returnSolutions) {
			isLocal = false;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();

			OWLClassExpression exp = axiom.getDomain();
			LocalityInfo locInfo = isTopClass(exp);
			if (locInfo.is()) {
				isLocal = true;
			} else {
				if (locInfo.canMake()) {
					solutions.addAll(locInfo.getSolutions());
				}
			}

			if (!isLocal) {
				OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
				if (!externalSignature.contains(prop)) {
					isLocal = true;
					solutions = new LinkedList<Set<OWLEntity>>();
				} else {
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			}
		} else {
			isLocal = !externalSignature.contains(axiom.getProperty()
					.getNamedProperty()) || isTopClass(axiom.getDomain()).is();
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLDataPropertyDomainAxiom axiom) {
		// An OWLDataPropertyDomainAxiom is bot-local iff the property does not
		// belong to the external signature or the domain is locally positive
		if (returnSolutions) {
			isLocal = false;
			canMakeLocal = true; // ultimately we can always make this axiom
									// local by removing the property from the
									// externalSignature
			solutions = new LinkedList<Set<OWLEntity>>();

			OWLDataProperty prop = axiom.getProperty().asOWLDataProperty();
			if (!externalSignature.contains(prop)) {
				isLocal = true;
			} else {
				LocalityInfo locInfo = isTopClass(axiom.getDomain());
				if (locInfo.is()) {
					isLocal = true;
				} else {
					solutions.addAll(locInfo.getSolutions());
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			}
		} else {
			isLocal = !externalSignature.contains(axiom.getProperty()
					.asOWLDataProperty()) || isTopClass(axiom.getDomain()).is();
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLObjectPropertyRangeAxiom axiom) {
		// An OWLObjectPropertyRangeAxiom is bot-local iff the property does not
		// belong to the external signature or the range is locally positive
		if (returnSolutions) {
			isLocal = false;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();

			OWLObjectProperty prop = axiom.getProperty().getNamedProperty();
			if (!externalSignature.contains(prop)) {
				isLocal = true;
			} else {
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
				LocalityInfo locInfo = isTopClass(axiom.getRange());
				if (locInfo.is()) {
					isLocal = true;
					solutions = new LinkedList<Set<OWLEntity>>();
				} else {
					if (locInfo.canMake()) {
						solutions.addAll(locInfo.getSolutions());
					}
				}
			}
		} else {
			isLocal = !externalSignature.contains(axiom.getProperty()
					.getNamedProperty()) || isTopClass(axiom.getRange()).is();
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLDataPropertyRangeAxiom axiom) {
		// An OWLDataPropertyRangeAxiom is bottom-local iff the property does
		// not belong to the external signature - the range can never be locally
		// negative because it's a datatype, not a class
		if (returnSolutions) {
			OWLDataProperty prop = axiom.getProperty().asOWLDataProperty();
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (!externalSignature.contains(prop)) {
				isLocal = true;
			} else {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(prop);
				solutions.add(aux);
			}
		} else {
			isLocal = !externalSignature.contains(axiom.getProperty()
					.asOWLDataProperty());
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(OWLSubPropertyChainOfAxiom axiom) {
		// An OWLSubPropertyChainOfAxiom axiom is bot-local iff at least one of
		// the properties in the chain does not belong to the external signature
		if (returnSolutions) {
			isLocal = false;
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();

			OWLEntity aux;
			Set<OWLEntity> auxSet;
			Set<OWLObjectPropertyExpression> seen = new HashSet<OWLObjectPropertyExpression>();

			for (OWLObjectPropertyExpression propExp : axiom.getPropertyChain()) {
				aux = propExp.getNamedProperty();
				if (!seen.contains(propExp)) {
					seen.add(propExp);
					if (!externalSignature.contains(aux)) {
						isLocal = true;
						solutions = new LinkedList<Set<OWLEntity>>();
						return;
					} else {
						auxSet = new HashSet<OWLEntity>();
						auxSet.add(aux);
						solutions.add(auxSet);
					}
				}
				// else we have already found propExp in the chain before and
				// dont need to look at it twice
			}
		} else {
			isLocal = false;
			Set<OWLObjectPropertyExpression> seen = new HashSet<OWLObjectPropertyExpression>();
			for (OWLObjectPropertyExpression propExp : axiom.getPropertyChain()) {
				if (!seen.contains(propExp)) {
					seen.add(propExp);
					if (!externalSignature.contains(propExp.getNamedProperty())) {
						isLocal = true;
						return;
					}
				}
			}
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	// End Property Axioms
	// ---------------------------------------------------------------

	/*
	 * OTHERS
	 */

	public void visit(OWLDeclarationAxiom axiom) {
		// An OWLDeclarationAxiom is bot-local iff the declared entity does not
		// belong to the foreign signature
		if (returnSolutions) {
			OWLEntity ent = axiom.getEntity();
			canMakeLocal = true;
			solutions = new LinkedList<Set<OWLEntity>>();
			if (!externalSignature.contains(ent)) {
				isLocal = true;
			} else {
				isLocal = false;
				Set<OWLEntity> aux = new HashSet<OWLEntity>();
				aux.add(ent);
				solutions.add(aux);
			}
		} else {
			isLocal = !externalSignature.contains(axiom.getEntity());
			canMakeLocal = isLocal;
			solutions = new LinkedList<Set<OWLEntity>>();
		}
	}

	public void visit(SWRLRule axiom) {
		// Currently, a SWRLRule axiom is always considered not bottom-local
		isLocal = false;
		canMakeLocal = false;
		solutions = new LinkedList<Set<OWLEntity>>();
	}

	public void visit(OWLHasKeyAxiom axiom) {
		// Currently, a HasKey axiom is always considered not bottom-local
		isLocal = false;
		canMakeLocal = false;
		solutions = new LinkedList<Set<OWLEntity>>();
	}

	public void visit(OWLDatatypeDefinitionAxiom axiom) {
		// Currently, a OWLDatatypeDefinition axiom is always considered
		// non-local
		isLocal = false;
		canMakeLocal = false;
		solutions = new LinkedList<Set<OWLEntity>>();
	}

	/*
	 * ------------------------------------------------ ASSERTION AXIOMS - we
	 * don't really care about these, since we eliminate this kind of axiom from
	 * the start -------------------------------------------------
	 */

	public void visit(OWLClassAssertionAxiom axiom) {
		/*
		 * //An OWLClassAssertionAxiom is bot-local if the class is locally
		 * positive, considering foreign entities bottom LocalityInfo auxInfo =
		 * isTopClass(axiom.getClassExpression()); isLocal = auxInfo.is();
		 * 
		 * if (isLocal){ canMakeLocal = true; solutions = new
		 * LinkedList<Set<OWLEntity>>(); } else{ canMakeLocal =
		 * auxInfo.canMake(); solutions = auxInfo.getSolutions(); }
		 */
	}

	public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
		/*
		 * isLocal = false;
		 * 
		 * if (isLocal){ canMakeLocal = true; solutions = new
		 * LinkedList<Set<OWLEntity>>(); } else{ canMakeLocal = false; solutions
		 * = new LinkedList<Set<OWLEntity>>(); }
		 * 
		 * //suggestedInformation =
		 * "An OWLNegativeDataPropertyAssertionAxiom is always not bottom local."
		 * ;
		 */
	}

	public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
		/*
		 * isLocal = false; canMakeLocal = isLocal; solutions = new
		 * LinkedList<Set<OWLEntity>>();
		 * 
		 * //suggestedInformation =
		 * "An OWLNegativeObjectPropertyAssertionAxiom is always not bottom local."
		 * ;
		 */
	}

	public void visit(OWLObjectPropertyAssertionAxiom axiom) {
		/*
		 * isLocal = false; canMakeLocal = isLocal; solutions = new
		 * LinkedList<Set<OWLEntity>>();
		 * 
		 * //suggestedInformation =
		 * "An OWLObjectPropertyAssertionAxiom is always not bottom local.";
		 */
	}

	public void visit(OWLDataPropertyAssertionAxiom axiom) {
		/*
		 * isLocal = false; canMakeLocal = isLocal; solutions = new
		 * LinkedList<Set<OWLEntity>>();
		 * 
		 * //suggestedInformation =
		 * "An OWLDataPropertyAssertionAxiom is always not bottom local.";
		 */
	}

	public void visit(OWLSameIndividualAxiom axiom) {
		/*
		 * isLocal = false; canMakeLocal = isLocal; solutions = new
		 * LinkedList<Set<OWLEntity>>();
		 * 
		 * //suggestedInformation =
		 * "An OWLSameIndividualsAxiom is always not bottom local.";
		 */
	}

	public void visit(OWLDifferentIndividualsAxiom axiom) {
		/*
		 * isLocal = false; canMakeLocal = isLocal; solutions = new
		 * LinkedList<Set<OWLEntity>>();
		 * 
		 * //suggestedInformation =
		 * "An OWLDifferentIndividualsAxiom is always not bottom local.";
		 */
	}

	/* End Assertion Axioms */
	// ------------------------------------------------------------------------

	/*
	 * ---------------------- ANNOTATION AXIOMS - useless for classification, we
	 * already removed them when first loading the ontology
	 * ----------------------
	 */

	public void visit(OWLAnnotationAssertionAxiom axiom) {
		/*
		 * isLocal = true; canMakeLocal = true; solutions = new
		 * LinkedList<Set<OWLEntity>>();
		 */
	}

	public void visit(OWLSubAnnotationPropertyOfAxiom axiom) {
		/*
		 * isLocal = true; //because we ignore annotations!! canMakeLocal =
		 * true; solutions = new LinkedList<Set<OWLEntity>>();
		 */
	}

	public void visit(OWLAnnotationPropertyDomainAxiom axiom) {
		/*
		 * isLocal = true; //because we ignore annotations!! canMakeLocal =
		 * true; solutions = new LinkedList<Set<OWLEntity>>();
		 */
	}

	public void visit(OWLAnnotationPropertyRangeAxiom axiom) {
		/*
		 * isLocal = true; //because we ignore annotations!! canMakeLocal =
		 * true; solutions = new LinkedList<Set<OWLEntity>>();
		 */
	}

	/*
	 * END ANNOTATIONS ------------------------------------
	 */

	// ----------------------------

	private class BottomChecker implements OWLClassExpressionVisitor {

		public boolean isBottom;
		public boolean canMakeBottom;
		public List<Set<OWLEntity>> solutions; // solutions will NEVER contain a
												// set whose intersection with
												// the externalSignature is
												// nonempty

		public LocalityInfo info() {
			return new LocalityInfo(isBottom, canMakeBottom, solutions);
		}

		public void visit(OWLClass exp) {
			// An OWLClass concept is locally bottom wrt a signature iff the
			// concept is not in that signature
			if (returnSolutions) {
				if (exp.isOWLThing()) {
					isBottom = false;
					canMakeBottom = false;
					solutions = new LinkedList<Set<OWLEntity>>();
				} else {
					canMakeBottom = true;
					solutions = new LinkedList<Set<OWLEntity>>();
					if (externalSignature.contains(exp)) {
						isBottom = false;
						Set<OWLEntity> aux = new HashSet<OWLEntity>();
						aux.add(exp);
						solutions.add(aux);
					} else
						isBottom = true;
				}
			} else {
				if (exp.isOWLThing())
					isBottom = false;
				else
					isBottom = !externalSignature.contains(exp);
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectIntersectionOf exp) {
			// An OWLObjectIntersectionOf concept is locally negative if at
			// least one conjunct is locally negative
			if (returnSolutions) {
				isBottom = false;
				boolean canBoolAcc = false;
				List<Set<OWLEntity>> auxList = new LinkedList<Set<OWLEntity>>();
				Iterator<OWLClassExpression> iterator = exp.asConjunctSet()
						.iterator();
				OWLClassExpression conjunct;

				while (iterator.hasNext() && !isBottom) {
					conjunct = iterator.next();
					conjunct.accept(this);
					if (!isBottom && canMakeBottom) {
						auxList.addAll(solutions);
						canBoolAcc = true;
					}
				}

				canMakeBottom = canBoolAcc || isBottom;

				if (!isBottom && canMakeBottom)
					solutions = auxList;
				else
					solutions = new LinkedList<Set<OWLEntity>>();
			} else {
				isBottom = false;
				Iterator<OWLClassExpression> iterator = exp.asConjunctSet()
						.iterator();
				// OWLClassExpression conjunct;
				while (iterator.hasNext() && !isBottom) {
					iterator.next().accept(this);
					// conjunct = iterator.next();
					// conjunct.accept(this);
				}
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectUnionOf exp) {
			// An OWLObjectUnionOf concept is locally negative iff all disjuncts
			// are locally negative
			if (returnSolutions) {
				LocalityInfo locInfo;
				isLocal = true;
				canMakeLocal = true;
				List<List<Set<OWLEntity>>> solsForBottom = new LinkedList<List<Set<OWLEntity>>>();
				for (OWLClassExpression classExp : exp.getOperands()) {
					locInfo = isBottomClass(classExp);
					isLocal = isLocal && locInfo.is();
					canMakeLocal = canMakeLocal && locInfo.canMake();
					solsForBottom.add(locInfo.getSolutions());
				}
				if (isLocal || !canMakeLocal)
					solutions = new LinkedList<Set<OWLEntity>>();
				else {
					ListProcessor listProc = new ListProcessor();
					solutions = listProc
							.getAllCombinations(solsForBottom, true);
				}
			} else {
				isLocal = true;
				for (OWLClassExpression classExp : exp.getOperands())
					isLocal = isLocal && isBottomClass(classExp).is();
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectComplementOf exp) {
			// An OWLObjectComplementOf concept is locally negative iff the
			// negated concept is locally positive
			if (returnSolutions) {
				exp.getOperand().accept(positiveVisitor);
				LocalityInfo locInfo = positiveVisitor.info();

				isBottom = locInfo.is();
				canMakeBottom = locInfo.canMake();
				solutions = locInfo.getSolutions();
			} else {
				exp.getOperand().accept(positiveVisitor);
				isBottom = positiveVisitor.info().is();
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		@Override
		public void visit(OWLObjectOneOf exp) {
			// An OWLObjectOneOf concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectAllValuesFrom exp) {
			// An OWLObjectAllValuesFrom concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLDataAllValuesFrom exp) {
			// An OWLDataAllValuesFrom concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectSomeValuesFrom exp) {
			// An OWLObjectSomeValuesFrom concept is locally negative iff the
			// property or the concept is locally negative
			if (returnSolutions) {
				exp.getFiller().accept(this);
				if (!isBottom) {
					OWLObjectProperty prop = exp.getProperty()
							.getNamedProperty();
					canMakeBottom = true;
					if (!externalSignature.contains(prop)) {
						isBottom = true;
						solutions = new LinkedList<Set<OWLEntity>>();
					} else {
						Set<OWLEntity> aux = new HashSet<OWLEntity>();
						aux.add(prop);
						solutions.add(aux);
					}
				}
			} else {
				exp.getFiller().accept(this);
				if (!isBottom)
					isBottom = !externalSignature.contains(exp.getProperty()
							.getNamedProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLDataSomeValuesFrom exp) {
			// An OWLDataSomeValuesFrom concept is locally negative iff the
			// property is locally negative
			if (returnSolutions) {
				OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
				canMakeBottom = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				if (!externalSignature.contains(prop))
					isBottom = true;
				else {
					isBottom = false;
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			} else {
				isBottom = !externalSignature.contains(exp.getProperty()
						.asOWLDataProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectHasSelf exp) {
			// An OWLObjectHasSelf concept is locally negative iff the property
			// is locally negative
			if (returnSolutions) {
				canMakeBottom = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				OWLObjectProperty prop = exp.getProperty().getNamedProperty();
				if (!externalSignature.contains(prop))
					isBottom = true;
				else {
					isBottom = false;
					Set<OWLEntity> auxSet = new HashSet<OWLEntity>();
					auxSet.add(prop);
					solutions.add(auxSet);
				}
			} else {
				isBottom = !externalSignature.contains(exp.getProperty()
						.getNamedProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectHasValue exp) {
			// An OWLObjectHasValue concept is locally negative iff the property
			// is locally negative - it's not possible to interpret an
			// individual as bottom
			if (returnSolutions) {
				isBottom = false;
				canMakeBottom = true;
				solutions = new LinkedList<Set<OWLEntity>>();

				OWLObjectProperty prop = exp.getProperty().getNamedProperty();
				Set<OWLEntity> auxSet;

				if (!externalSignature.contains(prop))
					isBottom = true;
				else {
					auxSet = new HashSet<OWLEntity>();
					auxSet.add(prop);
					solutions.add(auxSet);
				}
			} else {
				isBottom = !externalSignature.contains(exp.getProperty()
						.getNamedProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLDataHasValue exp) {
			// An OWLObjectHasValue concept is locally negative iff the property
			// is locally negative
			if (returnSolutions) {
				isBottom = false;
				canMakeBottom = true;
				solutions = new LinkedList<Set<OWLEntity>>();

				OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
				Set<OWLEntity> auxSet;

				if (!externalSignature.contains(prop))
					isBottom = true;
				else {
					auxSet = new HashSet<OWLEntity>();
					auxSet.add(prop);
					solutions.add(auxSet);
				}
			} else {
				isBottom = !externalSignature.contains(exp.getProperty()
						.asOWLDataProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectMinCardinality exp) {
			// An OWLObjectMinCardinality concept is locally negative iff the
			// property (or the filler, if it's qualified) is locally negative
			if (returnSolutions) {
				exp.getFiller().accept(this);
				if (!isBottom) {
					canMakeBottom = true;
					OWLObjectProperty prop = exp.getProperty()
							.getNamedProperty();
					if (externalSignature.contains(prop)) {
						Set<OWLEntity> aux = new HashSet<OWLEntity>();
						aux.add(prop);
						solutions.add(aux);
					} else {
						isBottom = true;
						solutions = new LinkedList<Set<OWLEntity>>();
					}
				}
			} else {
				exp.getFiller().accept(this);
				if (!isBottom)
					isBottom = !externalSignature.contains(exp.getProperty()
							.getNamedProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLDataMinCardinality exp) {
			// An OWLDataMinCardinality concept is locally negative iff the
			// property is locally negative
			if (returnSolutions) {
				canMakeBottom = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
				if (externalSignature.contains(prop)) {
					isBottom = false;
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				} else
					isBottom = true;
			} else {
				isBottom = !externalSignature.contains(exp.getProperty()
						.asOWLDataProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectMaxCardinality exp) {
			// An OWLObjectMaxCardinality concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLDataMaxCardinality exp) {
			// An OWLDataMaxCardinality concept is never locally negative
			isBottom = false;
			canMakeBottom = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectExactCardinality exp) {
			// An OWLObjectMinCardinality concept is locally negative iff the
			// property (or the filler, if it's qualified) is locally negative
			if (returnSolutions) {
				OWLObjectProperty prop;
				Set<OWLEntity> aux;
				isBottom = false;
				solutions = new LinkedList<Set<OWLEntity>>();

				if (exp.isQualified()) {
					exp.getFiller().accept(this);
				}
				if (!isBottom) {
					prop = exp.getProperty().getNamedProperty();
					if (externalSignature.contains(prop)) {
						canMakeBottom = true;
						aux = new HashSet<OWLEntity>();
						aux.add(prop);
						solutions.add(aux);
					} else {
						isBottom = true;
						canMakeBottom = true;
						solutions = new LinkedList<Set<OWLEntity>>();
					}
				}
			} else {
				exp.getFiller().accept(this);
				if (!isBottom)
					isBottom = !externalSignature.contains(exp.getProperty()
							.getNamedProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLDataExactCardinality exp) {
			// An OWLDataExactCardinality concept is locally negative iff the
			// property is locally negative
			if (returnSolutions) {
				OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
				canMakeBottom = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				if (externalSignature.contains(prop)) {
					isBottom = false;
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(exp.getProperty().asOWLDataProperty());
					solutions.add(aux);
				} else
					isBottom = true;
			} else {
				isBottom = !externalSignature.contains(exp.getProperty()
						.asOWLDataProperty());
				canMakeBottom = isBottom;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

	}

	// --------------------------------

	public class TopChecker implements OWLClassExpressionVisitor {

		public boolean isTop;
		public boolean canMakeTop;
		public List<Set<OWLEntity>> solutions;// solutions will NEVER contain a
												// set whose intersection with
												// the externalSignature is
												// nonempty

		public LocalityInfo info() {
			return new LocalityInfo(isTop, canMakeTop, solutions);
		}

		public void visit(OWLClass exp) { // checked
			// An OWLClass is never locally positive
			isTop = exp.isOWLThing();
			canMakeTop = isTop;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectIntersectionOf exp) {
			// An OWLObjectIntersection concept is locally positive iff all the
			// operands are locally positive
			if (returnSolutions) {
				LocalityInfo locInfo;
				isTop = true;
				canMakeTop = true;
				List<List<Set<OWLEntity>>> solsForTop = new LinkedList<List<Set<OWLEntity>>>();
				for (OWLClassExpression classExp : exp.getOperands()) {
					locInfo = isTopClass(classExp);
					isTop = isTop && locInfo.is();
					canMakeTop = canMakeTop && locInfo.canMake();
					solsForTop.add(locInfo.getSolutions());
				}
				if (isTop || !canMakeTop)
					solutions = new LinkedList<Set<OWLEntity>>();
				else {
					ListProcessor listProc = new ListProcessor();
					solutions = listProc.getAllCombinations(solsForTop, true);
				}
			} else {
				isTop = true;
				for (OWLClassExpression classExp : exp.getOperands())
					isTop = isTop && isTopClass(classExp).is();
				canMakeTop = isTop;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectUnionOf exp) {
			// An OWLObjectIntersection concept is locally positive iff at least
			// of the operands is locally positive
			if (returnSolutions) {
				isTop = false;
				boolean canBoolAcc = false;
				List<Set<OWLEntity>> auxList = new LinkedList<Set<OWLEntity>>();
				Iterator<OWLClassExpression> iterator = exp.getOperands()
						.iterator();
				OWLClassExpression conjunct;

				while (iterator.hasNext() && !isTop) {
					conjunct = iterator.next();
					conjunct.accept(this);
					if (!isTop && canMakeTop) {
						auxList.addAll(solutions);
						canBoolAcc = true;
					}
				}

				canMakeTop = canBoolAcc || isTop;

				if (!isTop && canMakeTop)
					solutions = auxList;
				else
					solutions = new LinkedList<Set<OWLEntity>>();
			} else {
				isTop = false;
				Iterator<OWLClassExpression> iterator = exp.getOperands()
						.iterator();
				// OWLClassExpression conjunct;
				while (iterator.hasNext() && !isTop) {
					iterator.next().accept(this);
					// conjunct = iterator.next();
					// conjunct.accept(this);
				}
				canMakeTop = isTop;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectComplementOf exp) {
			// An OWLObjectComplementOf concept is locally positive iff the
			// negated concept is locally negative
			if (returnSolutions) {
				exp.getOperand().accept(negativeVisitor);
				LocalityInfo locInfo = negativeVisitor.info();
				isTop = locInfo.is();
				canMakeTop = locInfo.canMake();
				solutions = locInfo.getSolutions();
			} else {
				exp.getOperand().accept(negativeVisitor);
				isTop = negativeVisitor.info().is();
				canMakeTop = isTop;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectOneOf exp) {
			// An OWLObjectOneOf concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLDataOneOf exp) {
			// An OWLDataOneOf concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectAllValuesFrom exp) {
			// An OWLObjectAllValueFrom concept is locally positive iff the
			// property is locally negative or the filler is locally positive
			if (returnSolutions) {
				exp.getFiller().accept(this);
				if (!isTop) {
					OWLObjectProperty prop = exp.getProperty()
							.getNamedProperty();
					if (!externalSignature.contains(prop)) {
						isTop = true;
						canMakeTop = true;
						solutions = new LinkedList<Set<OWLEntity>>();
					} else {
						canMakeTop = true;
						Set<OWLEntity> aux = new HashSet<OWLEntity>();
						aux.add(prop);
						solutions.add(aux);
					}
				}
			} else {
				exp.getFiller().accept(this);
				if (!isTop)
					isTop = !externalSignature.contains(exp.getProperty()
							.getNamedProperty());
				canMakeTop = isTop;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLDataAllValuesFrom exp) {
			// An OWLDataAllValueFrom concept is locally positive iff the
			// property is locally negative
			if (returnSolutions) {
				OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
				canMakeTop = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				if (!externalSignature.contains(prop))
					isTop = true;
				else {
					isTop = false;
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			} else {
				isTop = !externalSignature.contains(exp.getProperty()
						.asOWLDataProperty());
				canMakeTop = isTop;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectSomeValuesFrom exp) {
			// An OWLObjectSomeValuesFrom concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLDataSomeValuesFrom exp) {
			// An OWLDataSomeValuesFrom concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectHasSelf exp) {
			// An OWLObjectHasSelf concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectHasValue exp) {
			// An OWLObjectHasValue concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLDataHasValue exp) {
			// An OWLDataHasValue concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectMinCardinality exp) {
			// An OWLObjectMinCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLDataMinCardinality exp) {
			// An OWLDataMinCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLObjectMaxCardinality exp) {
			// An OWLObjectMaxCardinality concept is locally positive iff the
			// property or the filler concept is locally negative
			if (returnSolutions) {
				LocalityInfo locInfo = isBottomClass(exp.getFiller());
				isTop = locInfo.is();
				solutions = locInfo.getSolutions();
				canMakeTop = true;

				if (!isTop) {
					OWLObjectProperty prop = exp.getProperty()
							.getNamedProperty();
					if (!externalSignature.contains(prop)) {
						isTop = true;
						solutions = new LinkedList<Set<OWLEntity>>();
					} else {
						Set<OWLEntity> aux = new HashSet<OWLEntity>();
						aux.add(prop);
						solutions.add(aux);
					}
				}
			} else {
				isTop = isBottomClass(exp.getFiller()).is();
				if (!isTop)
					isTop = !externalSignature.contains(exp.getProperty()
							.getNamedProperty());
				canMakeTop = isTop;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLDataMaxCardinality exp) {
			// An OWLDataMaxCardinality concept is locally positive iff the
			// property is locally negative
			if (returnSolutions) {
				OWLDataProperty prop = exp.getProperty().asOWLDataProperty();
				canMakeTop = true;
				solutions = new LinkedList<Set<OWLEntity>>();
				if (!externalSignature.contains(prop))
					isTop = true;
				else {
					Set<OWLEntity> aux = new HashSet<OWLEntity>();
					aux.add(prop);
					solutions.add(aux);
				}
			} else {
				isTop = !externalSignature.contains(exp.getProperty()
						.asOWLDataProperty());
				canMakeTop = isTop;
				solutions = new LinkedList<Set<OWLEntity>>();
			}
		}

		public void visit(OWLObjectExactCardinality desc) {
			// An OWLObjectExactCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

		public void visit(OWLDataExactCardinality desc) {
			// An OWLDataExactCardinality concept is never locally positive
			isTop = false;
			canMakeTop = false;
			solutions = new LinkedList<Set<OWLEntity>>();
		}

	}

}
