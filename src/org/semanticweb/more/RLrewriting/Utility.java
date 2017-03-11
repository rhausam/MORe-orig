package org.semanticweb.more.RLrewriting;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.HermiT.model.Atom;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.util.AutoIRIMapper;

public class Utility {

	public static final int FLY = 0;
	public static final int UOBM = 1;
	public static final int LUBM = 2;
	public static final int AEO = 3;
	public static final int WINE = 4;

	public static OWLOntology loadOntology(String fileName) {
		AutoIRIMapper mapper = new AutoIRIMapper(new File(fileName.substring(0,
				fileName.lastIndexOf('/'))), false);
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		manager.addIRIMapper(mapper);
		// System.out.println(mapper.getDocumentIRI(IRI.create("http://semantics.crl.ibm.com/univ-bench-dl.owl")));
		OWLOntology ontology = null;
		try {
			ontology = manager.loadOntologyFromOntologyDocument(new File(
					fileName));
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		// manager.removeIRIMapper(mapper);
		return ontology;
	}

	public static Set<Atom> toSet(Atom[] data) {
		HashSet<Atom> ret = new HashSet<Atom>();
		for (Atom element : data)
			ret.add(element);
		return ret;
	}

	static PrintStream out = null;

	public static void redirectSystemOut() {
		String stamp = new SimpleDateFormat("HH:mm:ss").format(new Date());
		File test = new File("./output/console" + stamp + ".txt");
		try {
			out = new PrintStream(new FileOutputStream(test));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			return;
		}
		System.setOut(out);
	}

	public static void flushSystemOut() {
		if (out != null)
			out.flush();
	}

	public static void closeSystemOut() {
		if (out != null)
			out.close();
	}

	public static void sparql2expression(String input, String output)
			throws IOException {
		BufferedReader reader = new BufferedReader(new InputStreamReader(
				new FileInputStream(input)));
		BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(
				new FileOutputStream(output)));
		boolean first;
		String line, query;
		while ((line = reader.readLine()) != null) {
			if (line.startsWith("^")) {
				for (int i = 0; i < 4; ++i)
					line = reader.readLine();
				first = true;
				query = "";
				while (!(line = reader.readLine()).startsWith("}"))
					if (first) {
						first = false;
						query = expression(line.trim());
					} else
						query += ", " + expression(line.trim());
				writer.write(query);
				writer.newLine();
			}
		}
		reader.close();
		writer.close();
	}

	private static String expression(String line) {
		String[] parts = line.split(" ");
		if (parts[1].equals("rdf:type")) {
			return parts[2] + "(?" + variableIndex(parts[0]) + ")";
		} else
			return parts[1] + "(?" + variableIndex(parts[0]) + ",?"
					+ variableIndex(parts[2]) + ")";
	}

	private static int asciiX = (int) 'X';

	private static int variableIndex(String exp) {
		char var = exp.charAt(1);
		return (int) var - asciiX;
	}

}
