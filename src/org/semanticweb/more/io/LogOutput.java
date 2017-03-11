package org.semanticweb.more.io;

public class LogOutput {

	private static boolean show_output = true;
	private static boolean show_output_always = true;

	public static void print(double d) {
		if (show_output)
			print(String.valueOf(d));
	}

	public static void print(int i) {
		if (show_output)
			print(String.valueOf(i));
	}

	public static void print(String str) {

		if (show_output)
			System.out.println(str);

	}

	public static void printError(String str) {

		// if (show_output)
		System.err.println(str);

	}

	public static void showOutpuLog(boolean show) {
		show_output = show;
	}

	public static void showOutpuLogAlways(boolean show) {
		show_output_always = show;
	}

	public static void printAlways(String str) {
		if (show_output_always)
			System.out.println(str);
	}

	private static String lastPrinted = "";

	public static void printNotSupported(String str) {
		if (show_output_always && !str.equals(lastPrinted)) {
			lastPrinted = str;
			System.out.println(str);
		}
	}

}
