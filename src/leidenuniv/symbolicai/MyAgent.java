package leidenuniv.symbolicai;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Vector;

import leidenuniv.symbolicai.logic.KB;
import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;
import leidenuniv.symbolicai.logic.Term;

public class MyAgent extends Agent {

	@Override
	public KB forwardChain(KB kb) {
		// This method should perform a forward chaining on the kb given as argument,
		// until no new facts are added to the KB.
		// It starts with an empty list of facts. When ready, it returns a new KB of
		// ground facts (bounded).
		// The resulting KB includes all deduced predicates, actions, additions and
		// deletions, and goals.
		// These are then processed by processFacts() (which is already implemented for
		// you)
		// processFacts() adds all the facts in a given knowledge base to the correct
		// knowledge base.
		// HINT: You should assume that forwardChain only allows *bound* predicates to
		// be added to the facts list for now.

		KB copy = new KB();
		Collection<HashMap<String, String>> allSubstitutions = new HashSet<>();
		HashMap<String, Predicate> facts = new HashMap<String, Predicate>();
		Vector<Predicate> conditions = new Vector<Predicate>();
		boolean op = false;

		for (int i = 0; i < kb.rules().size(); i++) {
			Sentence sentence = kb.rules().get(i);
			if (sentence.conditions.isEmpty()) {
				// copy.add(sentence); //niet per se nodig
				for (int j = 0; j < sentence.conclusions.size(); j++) {
					facts.put(sentence.conclusions.get(j).toString(),
							  sentence.conclusions.get(j));

				} // for j
			} // if
		} // for i

		while (!op) {
			op = true;
			for (int i = 0; i < kb.rules().size(); i++) {
				int count = facts.size();
				allSubstitutions = new HashSet<>();
				conditions = new Vector<Predicate>();
				HashMap<String, String> substitution = new HashMap<String, String>();
				conditions = kb.rules().get(i).conditions;
				// findAllSubstitions(allSubstitutions, substitution, conditions, facts);
				if (findAllSubstitions(allSubstitutions, substitution, conditions, facts)) {
					for (HashMap<String, String> sub : allSubstitutions) {
						for (int j = 0; j < kb.rules().get(i).conclusions.size(); j++) {
							Predicate pred = substitute(kb.rules().get(i).conclusions.get(j), sub);
							Sentence sen = new Sentence(pred.toString());
							copy.add(sen); // add to knowledge base
							facts.put(pred.toString(), pred); // add to facts

						} // for j
					} // for sub
				} // if any substitutions
				if (facts.size() != count)
					op = false;
				} // for i
				// System.out.println(copy); //text
		} // while

		return copy;
	}

	@Override
	public boolean findAllSubstitions(Collection<HashMap<String, String>> allSubstitutions,
			HashMap<String, String> substitution, Vector<Predicate> conditions, HashMap<String, Predicate> facts) {
		// Recursive method to find *all* valid substitutions for a vector of
		// conditions, given a set of facts
		// The recursion is over Vector<Predicate> conditions (so this vector gets
		// shorter and shorter, the farther you are with finding substitutions)
		// It returns true if at least one substitution is found (can be the empty
		// substitution, if nothing needs to be substituted to unify the conditions with
		// the facts)
		// allSubstitutions is a list of all substitutions that are found, which was
		// passed by reference (so you use it build the list of substitutions)
		// substitution is the one we are currently building recursively.
		// conditions is the list of conditions you still need to find a subst for (this
		// list shrinks the further you get in the recursion).
		// facts is the list of predicates you need to match against (find substitutions
		// so that a predicate form the conditions unifies with a fact)

		boolean result;
		HashMap<String, String> copySubstitution = new HashMap<String, String>();

		if (conditions.isEmpty()) {
			copySubstitution.putAll(substitution);
			allSubstitutions.add(copySubstitution);
			return true;

		} // if stop

		else {
			result = false;
			Vector<Predicate> copy = new Vector<Predicate>();
			copy.addAll(conditions);
			Predicate condition = substitute(copy.firstElement(), substitution);
			copy.remove(0);
			HashMap<String, String> unification = new HashMap<String, String>();

			if (condition.not) {
				if (condition.not())
					result = findAllSubstitions(allSubstitutions, substitution, conditions, facts);
			} // if not

			else if (condition.eql) {
				if (condition.eql())
					result = findAllSubstitions(allSubstitutions, substitution, conditions, facts);
			} // else if eql

			else if (condition.neg) {
				for (Predicate fact : facts.values()) {
					if (unifiesWith(condition, fact) != null) {
						return false;
					}//if
				}//for
			}//else if neg

			else {
				for (Predicate fact : facts.values()) {
					copySubstitution = new HashMap<String, String>();
					copySubstitution.putAll(substitution);
					unification = unifiesWith(condition, fact);
					if (unification != null) {
						copySubstitution.putAll(unification);
						result = result | findAllSubstitions(allSubstitutions, copySubstitution, copy, facts);
					} // if
				} // for
			} // else

			return result;
		} // else
	}

	@Override
	public HashMap<String, String> unifiesWith(Predicate p, Predicate f) {
		// Returns the valid substitution for which p predicate unifies with f
		// You may assume that Predicate f is fully bound (i.e., it has no variables
		// anymore)
		// The result can be an empty substitution, if no subst is needed to unify p
		// with f (e.g., if p an f contain the same constants or do not have any terms)
		// Please note because f is bound and p potentially contains the variables,
		// unifiesWith is NOT symmetrical
		// So: unifiesWith("human(X)","human(joost)") returns X=joost, while
		// unifiesWith("human(joost)","human(X)") returns null
		// If no subst is found it returns null

		HashMap<String, String> s = new HashMap<String, String>();
		boolean uni = true;
		if (!(p.getName().equals(f.getName())) || 
		    !(p.getTerms().size() == f.getTerms().size())) {
			return null;
		} // if name and terms size
		for (int i = 0; i < p.getTerms().size(); i++) {
			if (!p.getTerm(i).toString().equals(f.getTerm(i).toString())) {
				if ((s.containsKey(p.getTerm(i).toString()) && 
				     s.get(p.getTerm(i).toString()) != f.getTerm(i).toString()) || 
					 !p.getTerm(i).var) {
					uni = false;
				}//if 
				s.put(p.getTerm(i).toString(), f.getTerm(i).toString());
			}//if not the same term
		}// for
		if (uni)
			return s;
		return null;
	}

	@Override
	public Predicate substitute(Predicate old, HashMap<String, String> s) {
		// Substitutes all variable terms in predicate <old> for values in substitution
		// <s>
		// (only if a key is present in s matching the variable name of course)
		// Use Term.substitute(s)

		// bestaat er een key in s die terug komt in old
		// if ja check voor alle vectoren of ze een term in s gelijk hebben

		Predicate nieuw = new Predicate(old.toString());

		for (int i = 0; i < nieuw.getTerms().size(); i++) {
			nieuw.getTerm(i).substitute(s);
		} // for

		return nieuw;
	}

	@Override
	public Plan idSearch(int maxDepth, KB kb, Predicate goal) {
		// The main iterative deepening loop
		// Returns a plan, when the depthFirst call returns a plan for depth d.
		// Ends at maxDepth
		// Predicate goal is the goal predicate to find a plan for.
		// Return null if no plan is found.
		return null;
	}

	@Override
	public Plan depthFirst(int maxDepth, int depth, KB state, Predicate goal, Plan partialPlan) {
		// Performs a depthFirst search for a plan to get to Predicate goal
		// Is a recursive function, with each call a deeper action in the plan, building
		// up the partialPlan
		// Caps when maxDepth=depth
		// Returns (bubbles back through recursion) the plan when the state entails the
		// goal predicate
		// Returns null if capped or if there are no (more) actions to perform in one
		// node (state)
		// HINT: make use of think() and act() using the local state for the node in the
		// search you are in.
		return null;
	}
}
