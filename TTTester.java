// Bill Jameson (jamesw2@rpi.edu)
// TTTester.java
// main method to test capabilities of truth tree:
//   command-line based interactive truth tree builder

/* TODO (i.e., future enhancements):
 * -more robust validation on user input (esp. syntactical correctness of premises)
 * -add support for loading a set of premises from a file
 */

import java.util.InputMismatchException;
import java.util.Scanner;
import java.util.ArrayList;

public class TTTester {

	public static void main(String[] args) {
		System.out.print("Truth Tree Interface\n" + "Written by Bill Jameson (jamesw2@rpi.edu)\n\n");
		
		boolean loop = true;
		String input;
		ArrayList<TFStatement> premises = new ArrayList<TFStatement>();
		
		// get the premises for the truth tree from the user
		System.out.print("Enter premises for the truth tree using Slate-style prefix syntax:\n");
		do {
			boolean validInput = false;
			
			System.out.print("Premise " + (premises.size()+1) + ": ");
			input = readLine();
			
			premises.add(new TFStatement(input));
			
			System.out.print("Continue entering premises? (y/n) ");
			while (!validInput) {
				input = readLine();
				
				if (input.equalsIgnoreCase("n")) {
					loop = false;
					validInput = true;
				}
				else if (input.equalsIgnoreCase("y")) {
					loop = true;
					validInput = true;
				}
				else
					System.out.print("Invalid input. Type Y/y to continue, N/n to quit: ");
			}
		}
		while (loop);
		
		TruthTree tt = new TruthTree(premises);
		
		System.out.print("Enter commands to build the truth tree. Type help for a list of commands and" +
						 " their descriptions\n");
		loop = true;
		do {
			System.out.print("> ");
			input = readLine();
			
			if (input.equalsIgnoreCase("help")) {
				System.out.println("help - Show this list of commands and descriptions");
				System.out.println("print - Display the truth tree's current state");
				System.out.println("quit - Exit the program");
				System.out.println("expand - Try to expand a statement of the truth tree (you'll be "
								   + "prompted to specify which one)");
				System.out.println("close - Try to close a branch by specifying a statement and "
								   + "its negation");
				System.out.println("done - Validate that the truth tree has been completed (this will "
								   + "not quit the program)");
				loop = true;
			}
			else if (input.equalsIgnoreCase("print")) {
				System.out.println("Key: [O] next to a statement indicates that it's already been expanded, "
								   + "and [X] indicates that the branch it's listed next to is closed");
				tt.print();
				loop = true;
			}
			else if (input.equalsIgnoreCase("quit")) {
				loop = false;
			}
			else if (input.equalsIgnoreCase("expand")) {
				System.out.print("Enter the number of the statement to expand (-1 to cancel): ");
				int n = readInt();
				if (n != -1) {
					boolean success = tt.expand(n);
					if (!success) {
						System.out.println("Unable to expand the specified statement.");
						System.out.println("It may not be expandable, or it may have already been expanded.");
						System.out.println("Try using the print command to double-check.");
					}
				}
				loop = true;
			}
			else if (input.equalsIgnoreCase("close")) {
				System.out.print("Enter the number of the first statement (-1 to cancel):  ");
				int n1 = readInt();
				System.out.print("Enter the number of the second statement (-1 to cancel): ");
				int n2 = readInt();
				if (n1 != -1 && n2 != -1) {
					boolean success = tt.closeBranch(n1, n2);
					if (!success) {
						System.out.println("Unable to close any branches with the specified statements.");
						System.out.println("Use the print command to verify that the statements are in "
										   + "the same branch and one is the negation of the other.");
					}
				}
				loop = true;
			}
			else if (input.equalsIgnoreCase("done")) {
				boolean success = tt.checkDone();
				if (success)
					System.out.println("The tree appears to be complete.");
				else
					System.out.println("There are still some operations to be performed before the tree is done");
				loop = true;
			}
			else
				System.out.println("Invalid input. Try again.");
		}
		while (loop);
	}
	
	// read a line from the console
	public static String readLine() throws InputMismatchException {
		Scanner in = new Scanner(System.in);  
		String str;
		str = in.nextLine();
		return str;
	}
	
	public static int readInt() throws InputMismatchException {
		Scanner in = new Scanner(System.in);
		int n;
		n = in.nextInt();
		return n;
	}
}
