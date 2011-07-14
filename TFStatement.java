// Bill Jameson (jamesw2@rpi.edu)
// TFStatement.java
// A class that represents a statement in truth-functional logic/propositional calculus
/* Structured as a tree, with left and right nodes indicating simpler statements that form
 *   the left and right operands of binary operators
 * For unary operators, the left node will be the simpler statement and the right will be null
 * Syntax is Slate-style, fully parenthesized prefix notation
 *   e.g., (not (if (and P Q) (iff (or A B) R)))
 * Currently supports {and, or, not, if, iff}; {not} is unary and the rest are binary
 */

/* TODO (i.e., future enhancements):
 * -add support for generalized conjunctions/disjunctions
 * -use correct Unicode symbols for TF symbols (wedge for or, arrow for if, etc.)
 * -add a validator to check for syntactic correctness
 * -workaround for {iff, not iff} expansions needing to create an intermediate AND
 */

public class TFStatement {
	private StmtType type;				// type of statement
	private String stmt;				// full representation of statement
	private String lOp, rOp;			// representation of left/right operands for binary operators
	
	private TFStatement lStmt, rStmt;	// 
	
	// default constructor, for testing things
	public TFStatement() {
		type = StmtType.Atom;
		stmt = "P";
		lOp = "P";
		rOp = null;
		lStmt = rStmt = null;
	}
	
	// construct a TFStatement from a String recursively by progressively stripping parentheses
	// for now, assume no syntax errors
	public TFStatement(String repr) {
		stmt = repr;
		// parse repr, the representation of the statement
		if (!repr.startsWith("(")) {			// doesn't start w/ '(', so must be atomic
			type = StmtType.Atom;
			lOp = repr;
			rOp = null;
			lStmt = rStmt = null;
		}
		else if (repr.startsWith("(not")) {
			type = StmtType.Not;
			lOp = repr;
			rOp = null;
			
			// child is the substatment negated by the "not"
			// this substatement starts after "(not " and ends before the last ")"
			lStmt = new TFStatement(repr.substring(5, repr.length()-1));
			rStmt = null;
		}
		// for now, generalized conjunctions & disjunctions aren't supported, must be represented as nested
		// e.g., (and P (and Q R)) 
		else if (repr.startsWith("(and ")) {
			type = StmtType.And;
			
			String ops = repr.substring(5, repr.length()-1);	// cut off the leading "(and " and trailing ")"
			lOp = getFirstArg(ops);
			lStmt = new TFStatement(lOp);
			
			rOp = getFirstArg(ops.substring(lOp.length()+1, ops.length()));
			rStmt = new TFStatement(rOp);
		}
		else if (repr.startsWith("(or ")) {
			type = StmtType.Or;
			
			String ops = repr.substring(4, repr.length()-1);
			lOp = getFirstArg(ops);
			lStmt = new TFStatement(lOp);
			
			rOp = getFirstArg(ops.substring(lOp.length()+1, ops.length()));
			rStmt = new TFStatement(rOp);
		}
		else if (repr.startsWith("(if ")) {
			type = StmtType.If;
			
			String ops = repr.substring(4, repr.length()-1);
			lOp = getFirstArg(ops);
			lStmt = new TFStatement(lOp);
			
			rOp = getFirstArg(ops.substring(lOp.length()+1, ops.length()));
			rStmt = new TFStatement(rOp);
		}
		else if (repr.startsWith("(iff ")) {
			type = StmtType.Iff;
			
			String ops = repr.substring(5, repr.length()-1);
			lOp = getFirstArg(ops);
			lStmt = new TFStatement(lOp);
			
			rOp = getFirstArg(ops.substring(lOp.length()+1, ops.length()));
			rStmt = new TFStatement(rOp);
		}
		
	}
	
	public StmtType getType() { return type;  }
	public TFStatement getL() { return lStmt; }
	public TFStatement getR() { return rStmt; }
	
	// check if the statement will branch when decomposed
	public boolean branches() {
		boolean temp = false;
		if (type == StmtType.If)
			temp = true;
		else if (type == StmtType.Iff)
			temp = true;
		else if (type == StmtType.Or)
			temp = true;
		else if (type == StmtType.Not) {
			if (lStmt.type == StmtType.And)
				temp = true;
			else if (lStmt.type == StmtType.Iff)
				temp = true;
		}
		
		return temp;
	}
	
	// check if the current statement can be decomposed
	// the only types that can't are atomic (an atom or a negation of an atom)
	public boolean canExpand() {
		if (type == StmtType.Atom)
			return false;
		if (type == StmtType.Not && lStmt.type == StmtType.Atom)
			return false;
		
		return true;
	}
	
	// WIP (needs significant reworking to make less complicated b/c of the Iff cases
	// get the decomposition of statement
	/* due to limitations, if a decomposition branches and creates multiple entries on one branch, they
	 *   will be ANDed together, requiring an additional decomposition
	 */
	public TFStatement getLeftExp() {
		if (type == StmtType.Atom)
			return null;
		else {
			if ((type == StmtType.And) || (type == StmtType.Or))
				return lStmt;
			else if (type == StmtType.If)
				return new TFStatement("(not " + lOp + ")");
			else if (type == StmtType.Iff)
				return new TFStatement("(and " + lOp + " " + rOp + ")");
			else if (type == StmtType.Not) {
				if (lStmt.type == StmtType.Not)
					return lStmt.lStmt;
				else if ((lStmt.type == StmtType.And) || lStmt.type == StmtType.Or)
					return new TFStatement("(not " + lStmt.lOp + ")");
				else if (lStmt.type == StmtType.If)
					return lStmt.lStmt;
				else if (lStmt.type == StmtType.Iff)
					return new TFStatement("(and " + lStmt.lOp + " (not " + lStmt.rOp + "))");
			}
		}
		
		// null case (covers mostly atomics)
		return null;
	}
	public TFStatement getRightExp() {
		if (type == StmtType.Atom)
			return null;
		else {
			if ((type == StmtType.And) || (type == StmtType.Or))
				return rStmt;
			else if (type == StmtType.If)
				return rStmt;
			else if (type == StmtType.Iff)
				return new TFStatement("(and (not " + lOp + ") (not " + rOp + "))");
			else if (type == StmtType.Not) {
				if ((lStmt.type == StmtType.And) || lStmt.type == StmtType.Or)
					return new TFStatement("(not " + lStmt.rOp + ")");
				else if (lStmt.type == StmtType.If)
					return new TFStatement("(not " + lStmt.rOp + ")");
				else if (lStmt.type == StmtType.Iff)
					return new TFStatement("(and (not " + lStmt.lOp + ") " + lStmt.rOp + ")");
			}
		}
		
		// null case (covers mostly atomics, and {not not} here)
		return null;
	}
	
	// return a String representing the object
	public String toString() {
		if (type == StmtType.Atom)
			return stmt;
		else if (type == StmtType.Not) {
			boolean childAtomic = true;					// parenthesize operator if not atomic
			if (!(lStmt.getType() == StmtType.Atom))
				childAtomic = false;
			
			StringBuffer sb = new StringBuffer("~");
			if (!childAtomic)
				sb.append("(");
			sb.append(lStmt.toString());
			if (!childAtomic)
				sb.append(")");
			
			return new String(sb);
		}
		else if (type == StmtType.And) {
			boolean lChildAtomic = true, rChildAtomic = true;
			if (!(lStmt.getType() == StmtType.Atom))
				lChildAtomic = false;
			if (!(rStmt.getType() == StmtType.Atom))
				rChildAtomic = false;
			
			StringBuffer sb = new StringBuffer("");
			if (!lChildAtomic)
				sb.append("(");
			sb.append(lStmt.toString());
			if (!lChildAtomic)
				sb.append(")");
			sb.append(" ^ ");
			if (!rChildAtomic)
				sb.append("(");
			sb.append(rStmt.toString());
			if (!rChildAtomic)
				sb.append(")");
			
			return new String(sb);
		}
		else if (type == StmtType.Or) {
			boolean lChildAtomic = true, rChildAtomic = true;
			if (!(lStmt.getType() == StmtType.Atom))
				lChildAtomic = false;
			if (!(rStmt.getType() == StmtType.Atom))
				rChildAtomic = false;
			
			StringBuffer sb = new StringBuffer("");
			if (!lChildAtomic)
				sb.append("(");
			sb.append(lStmt.toString());
			if (!lChildAtomic)
				sb.append(")");
			sb.append(" v ");
			if (!rChildAtomic)
				sb.append("(");
			sb.append(rStmt.toString());
			if (!rChildAtomic)
				sb.append(")");
			
			return new String(sb);
		}
		else if (type == StmtType.If) {
			boolean lChildAtomic = true, rChildAtomic = true;
			if (!(lStmt.getType() == StmtType.Atom))
				lChildAtomic = false;
			if (!(rStmt.getType() == StmtType.Atom))
				rChildAtomic = false;
			
			StringBuffer sb = new StringBuffer("");
			if (!lChildAtomic)
				sb.append("(");
			sb.append(lStmt.toString());
			if (!lChildAtomic)
				sb.append(")");
			sb.append(" -> ");
			if (!rChildAtomic)
				sb.append("(");
			sb.append(rStmt.toString());
			if (!rChildAtomic)
				sb.append(")");
			
			return new String(sb);
		}
		else if (type == StmtType.Iff) {
			boolean lChildAtomic = true, rChildAtomic = true;
			if (!(lStmt.getType() == StmtType.Atom))
				lChildAtomic = false;
			if (!(rStmt.getType() == StmtType.Atom))
				rChildAtomic = false;
			
			StringBuffer sb = new StringBuffer("");
			if (!lChildAtomic)
				sb.append("(");
			sb.append(lStmt.toString());
			if (!lChildAtomic)
				sb.append(")");
			sb.append(" <-> ");
			if (!rChildAtomic)
				sb.append("(");
			sb.append(rStmt.toString());
			if (!rChildAtomic)
				sb.append(")");
			
			return new String(sb);
		}
		
		// fallback case (will never be reached, but makes the compiler happy)
		return stmt;
	}
	
	// check 2 TFStatements for equality
	// can be done based on the string representation (case-sensitive)
	// note: not to be mistaken for a check for the logical equivalence of two statements
	public boolean equals(TFStatement other) {
		return stmt.equals(other.stmt);
	}
	
	// get the first "argument" (parenthesized or not)
	public static String getFirstArg(String stmt) {
		int stmtIndex = 1, openParenCount = 0;		// openParenCount = tally of unclosed parentheses in substring
		StringBuffer sb = new StringBuffer("");
		
		String temp = stmt.substring(0, 1);
		sb.append(temp);
		
		// argument may be unparenthesized (i.e., an atomic statement)
		if (!temp.equalsIgnoreCase("(")) {
			while (!(temp.equalsIgnoreCase(" ") || temp.equalsIgnoreCase(")")) && stmtIndex < stmt.length()) {
				temp = stmt.substring(stmtIndex, stmtIndex+1);
				if (!(temp.equalsIgnoreCase(" ") || temp.equalsIgnoreCase(")")))
					sb.append(temp);
				stmtIndex++;
			}
			
			return new String(sb);
		}
		else
			openParenCount++;
	
		for (; stmtIndex < stmt.length(); stmtIndex++) {
			temp = stmt.substring(stmtIndex, stmtIndex+1);
			sb.append(temp);
			if (temp.equalsIgnoreCase("("))
				openParenCount++;
			else if (temp.equalsIgnoreCase(")"))
				openParenCount--;
			
			if (openParenCount == 0)
				break;
		}
		
		return new String(sb);
	}
}
