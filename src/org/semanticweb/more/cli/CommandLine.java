/* Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory

   This file is part of HermiT.

   HermiT is free software: you can redistribute it and/or modify
   it under the terms of the GNU Lesser General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   HermiT is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public License
   along with HermiT.  If not, see <http://www.gnu.org/licenses/>.
 */
package org.semanticweb.more.cli;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.semanticweb.more.MOReReasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.reasoner.InferenceType;

public class CommandLine {

	public static void main(String[] argv) throws FileNotFoundException,
			OWLOntologyStorageException {
		if (argv.length == 2) {
			File inputFile = new File(argv[0]);// IRI??
			File outputFile = new File(argv[1]);

			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			try {
				MOReReasoner MORe = new MOReReasoner(
						manager.loadOntologyFromOntologyDocument(inputFile));
				long tClassification = System.currentTimeMillis();
				MORe.precomputeInferences(InferenceType.CLASS_HIERARCHY);
				tClassification = System.currentTimeMillis() - tClassification;
				if (!outputFile.exists())
					try {
						outputFile.createNewFile();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				MORe.printHierarchy(outputFile);
				MORe.dispose();
			} catch (OWLOntologyCreationException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
		} else {
			System.out.println("Incorrect input");// Please introduce a URL for
													// the ontology you want to
													// classify and another for
													// the file where you want
													// the classification to be
													// output");
		}
	}

}
