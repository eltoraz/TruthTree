// Bill Jameson (jamesw2@rpi.edu)
// TruthTree.java
// Contains the TruthTree class, a wrapper for TTNodes that compose a truth tree,
//   and the TTNode, that represents an individual statement in a truth tree along with information
//   about the status of that statement (closed, expanded, etc.)

/* TODO (i.e., future enhancements):
 * -require less manual tracking of stuff
 * -find a better symbol (preferably a check mark) to replace [O] to mark expanded statements
 * -standardize the code more around the ArrayList (introduced later in development so some code finds
 *    IDs manually (etc.))
 * -add expansions for equivalence rules & rules of inference
 */

import java.util.ArrayList;

class TTNode {
	private TFStatement data;
	private TTNode parent, lChild, rChild;
	private boolean closed, expanded;
	private int id;
	
	private int branchedFrom;				// keep track of the node the current branch is an offshoot of
	private int depth;						// number of forks in current branch
	private char lOrRBranch;
	
	// note that these static variables will prevent multiple truth tree instances from existing simultaneously
	private static int nodeNextIndex = 1;	// number to use for the next node
	private static ArrayList<TTNode> nodeList = null;		// static list of nodes for easy access
	
	public TTNode(TFStatement init) {
		if (nodeList == null)
			nodeList = new ArrayList<TTNode>();
		data = init;
		parent = lChild = rChild = null;
		closed = expanded = false;
		id = nodeNextIndex++;
		branchedFrom = 0;					// dummy (for root, others will be changed manually)
		depth = 0;
		lOrRBranch = '?';
		
		nodeList.add(this);
	}
	
	// only use when initializing the tree, to add premises
	public void addPremise(TFStatement premise) {
		TTNode temp = this;
		while (temp.lChild != null)			// find the node with the last argument
			temp = temp.lChild;
		temp.lChild = new TTNode(premise);
		temp.lChild.parent = temp;
	}
	
	// recursively add a TFStatement to the tree as a result of an expansion
	private void addStmt(TFStatement lStmt, TFStatement rStmt, boolean branch) {
		if (closed)							// don't bother working on a closed branch
			return;
		if (!branch) {						// non-branching expansion
			if (rStmt == null) {
				if (lChild == null) {
					lChild = new TTNode(lStmt);
					lChild.parent = this;
					lChild.branchedFrom = branchedFrom;
					lChild.depth = depth;
					lChild.lOrRBranch = lOrRBranch;
				}
				else {
					lChild.addStmt(lStmt, rStmt, branch);
					if (rChild != null)		//  propagate through forks as well
						rChild.addStmt(lStmt, rStmt, branch);
				}
			}
			else {							// non-branching cases, adding 2 parts of expanded statement
				if (lChild == null) {
					lChild = new TTNode(lStmt);
					lChild.parent = this;
					lChild.branchedFrom = branchedFrom;
					lChild.depth = depth;
					lChild.lOrRBranch = lOrRBranch;
					lChild.addStmt(rStmt, null, false);
				}
				else {
					lChild.addStmt(lStmt, rStmt, branch);
					if (rChild != null)
						rChild.addStmt(lStmt, rStmt, branch);
				}
			}
		}
		else {								// branching cases, will assume that both statements are non-null
			if (lChild == null) {			// here, rChild will always be null as well
				lChild = new TTNode(lStmt);
				lChild.parent = this;
				lChild.branchedFrom = id;
				lChild.depth = depth+1;
				lChild.lOrRBranch = 'l';
				
				rChild = new TTNode(rStmt);
				rChild.parent = this;
				rChild.branchedFrom = id;
				rChild.depth = depth+1;
				rChild.lOrRBranch = 'r';
			}
			else {
				lChild.addStmt(lStmt, rStmt, branch);
				if (rChild != null)
					rChild.addStmt(lStmt, rStmt, branch);
			}
		}
	}
	
	public int getID() { return id; }
	
	// look for the numbered statement and try to expand it
	public boolean expand(int n) {
		if (n < 1 || n >= nodeNextIndex)
			return false;
		
		if (nodeList.get(n-1).expanded)
			return false;
		
		TTNode target = nodeList.get(n-1);
		boolean branched = target.data.branches();
		TFStatement left, right;
		
		left = target.data.getLeftExp();
		right = target.data.getRightExp();
		
		if (left == null && right == null)		// if both are null, no expansion
			return false;
		else if (right == null) {				// right only = null -> {not not} structure
			target.addStmt(left, null, false);
			target.expanded = true;
			return true;
		}
		else {
			if (branched) {								// if it branches, add the left to the left branch
				target.addStmt(left, right, true);		//   and the right to the right branch
				target.expanded = true;
				return true;
			}
			else {										// otherwise add both to the left (e.g., in the case
				target.addStmt(left, right, false);		//   of an AND
				target.expanded = true;
				return true;
			}
		}
	}
	
	// helper functions to close a branch
	// both should be called in succession when closing a branch:
	//   closeDesc() is the one that closes the current node (so it should be called first)
	private void closeAsc() {
		if (parent != null) {
			if (parent.depth == depth) {
				parent.closed = true;
				parent.closeAsc();
			}
			// normally, don't go to the parent branch, but can close the parent if both children
			//   are already closed
			else if (parent.rChild != null && parent.lChild.closed && parent.rChild.closed) {
				parent.closed = true;
				parent.closeAsc();
			}
		}
	}
	private void closeDesc() {
		closed = true;
		if (lChild != null)
			lChild.closeDesc();
		if (rChild != null)
			rChild.closeDesc();
	}
	
	// try to close the branch
	// note that the statements indicated need not be atomic
	public boolean closeBranch(int n1, int n2) {
		if (n1 < 1 || n2 < 1 || n1 >= nodeNextIndex || n2 > nodeNextIndex)
			return false;
		
		TTNode node1, node2;
		node1 = nodeList.get(n1-1);					// n-1 because ArrayLists are 0-indexed
		node2 = nodeList.get(n2-1);
		
		// at least one of them must be a negation
		if (node1.data.getType() != StmtType.Not && node2.data.getType() != StmtType.Not)
			return false;
		
		// make sure the nodes are on the same branch
		// compare by number: if on the same branch, the node with the smaller number must
		//   be an ancestor of the one with the larger number
		if (n1 < n2) {
			TTNode temp = node2;
			while (temp.parent != null) {			// check the tree up to the root
				if (temp.parent == node1)
					break;
				temp = temp.parent;
			}
			if (temp.parent == null)				// if the loop wasn't broken, it reached
				return false;						//   the root without finding node1, so they're
		}											//   on different branches
		else if (n1 > n2) {
			TTNode temp = node1;
			while (temp.parent != null) {
				if (temp.parent == node2)
					break;
				temp = temp.parent;
			}
			if (temp.parent == null)
				return false;
		}
		
		// check if one of the statements is the negation of the other
		if (node1.data.getType() == StmtType.Not) {
			if (node1.data.getL().equals(node2.data)) {
				if (n1 > n2) {						// close the branch of the node lower on the tree
					node1.closeDesc();
					node1.closeAsc();
				}
				else {
					node2.closeDesc();
					node2.closeAsc();
				}
				
				return true;
			}
		}
		if (node2.data.getType() == StmtType.Not) {
			if (node2.data.getL().equals(node1.data)) {
				if (n1 > n2) {
					node1.closeDesc();
					node1.closeAsc();
				}
				else {
					node2.closeDesc();
					node2.closeAsc();
				}
				
				return true;
			}
		}
		
		return false;
	}
	
	// check if the tree is finished (i.e., all statements expanded, or all branches closed)
	public boolean checkDone() {
		// if the root is closed, everything below it must be too
		if (nodeList.get(0).closed)
			return true;
		
		// if there exists a node in a non-closed branch that can be expanded, not done
		for (int i = 0; i < nodeList.size(); i++) {
			if (!nodeList.get(i).closed && nodeList.get(i).data.canExpand() && !nodeList.get(i).expanded)
				return false;
		}

		// check all node-node pairs within all branches to see if there are any to close
		// start at the bottom and work up the list, checking if the current is the negation of an ancestor
		//   or an ancestor is the negation of this
		for (int i = nodeList.size()-1; i >= 0; i--) {
			TTNode current = nodeList.get(i), temp;
			
			if (current.closed)
				continue;
			
			if (current.parent != null) {
				temp = current.parent;
				
				if (current.data.getType() == StmtType.Not) {	// this is the negation of an ancestor
					if (current.data.getL().equals(temp.data))
						return false;
				}
				if (temp.data.getType() == StmtType.Not){		// an ancestor is the negation of this
					if (temp.data.getL().equals(current.data))
						return false;
				}
			
				while (temp.parent != null) {
					temp = temp.parent;
					if (current.data.getType() == StmtType.Not) {
						if (current.data.getL().equals(temp.data)) {
							return false;
						}
					}
					if (temp.data.getType() == StmtType.Not){
						if (temp.data.getL().equals(current.data)) {
							return false;
						}
					}
				}
			}
		}
		
		// if the root isn't closed (and thus there is >= 1 open branch), and all statements
		//   have been decomposed, done
		return true;
	}
	
	// print the node (i.e., the value of its statement) and its children via DFS
	public void printDFS() {
		if (depth > 0)
			System.out.print(" ");
		for (int i = 0; i < depth; i++)
			System.out.print("-");
		if (branchedFrom > 0)
			System.out.print(" " + branchedFrom + lOrRBranch);
		System.out.print(" [" + id + "] " + data);
		if (expanded)
			System.out.print("\t[O]");
		System.out.print("\n");
		if (branchedFrom > 0 && closed && lChild == null) {
			System.out.print(" ");
			for (int i = 0; i < depth; i++)
				System.out.print("-");
			System.out.print(" " + branchedFrom + lOrRBranch + " [X]\n");
		}
		if (lChild != null)
			lChild.printDFS();
		if (rChild != null)
			rChild.printDFS();
	}
}


/********************* BEGIN TRUTH TREE CLASS ******************************/
public class TruthTree {
	private TTNode root;
	
	// default constructor, to make an empty truth tree
	public TruthTree() { root = null; }
	
	// create a truth tree whose root (first node) is the statement described by s
	public TruthTree(String s) { root = new TTNode(new TFStatement(s)); }
	
	// create a truth tree with the root as statement t
	public TruthTree(TFStatement t) { root = new TTNode(t); }
	
	// create a truth tree with the premises contained in the specified ArrayList
	public TruthTree(ArrayList<TFStatement> a) {
		root = new TTNode(a.get(0));
		for (int i = 1; i < a.size(); i++)
			addPremise(a.get(i));
	}
	
	// add a premise to the root (probably not a good idea to use these after you've begun expanding)
	public void addPremise(String s) { addPremise(new TFStatement(s)); }	
	public void addPremise(TFStatement t) {
		if (root == null)
			root = new TTNode(t);
		else
			root.addPremise(t); }
	
	// expand/decompose the numbered statement indicated
	public boolean expand(int n) { return root.expand(n); }
	
	// try to close branch based on the indicated statements
	public boolean closeBranch(int n1, int n2) { return root.closeBranch(n1, n2); }
	
	// check if the tree is done
	public boolean checkDone() { return root.checkDone(); }
	
	// print all the branches, via DFS
	public void print() { root.printDFS(); }
}
