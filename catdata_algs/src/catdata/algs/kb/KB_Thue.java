package catdata.algs.kb;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import catdata.algs.Pair;
import catdata.algs.Quad;

/**
 * @author Ryan Wisnesky
 * 
 *         Implementation of a Knuth-Bendix variant for Semi-Thue systems (monoid
 *         presentations), following the Kapur and Narendran 1985 paper.
 * 
 *         Note: In this variant of Knuth-Bendix, two terms can be equal without
 *         having the same normal form. Therefore, clients MUST use equiv
 *         instead of normalize followed by equals. normalize is provided for
 *         client convenience.
 *         
 *         Note: The constructor mutates the input words IN PLACE.
 * 
 * @param <Y> the alphabet
 */
public class KB_Thue<Y> {

	private Set<Pair<List<Y>, List<Y>>> rules;
	private boolean finished = false;
	private Map<Pair<List<Y>, List<Y>>, Boolean> equivs = new HashMap<>();
	private int max_iterations;
	private int iteration = 0;
	
	/**
	 * @param rules to be completed. DOE NOTE copy, and MUTATES IN PLACE the pairs inside of rules 
	 * @param max_iterations to run
	 */
	public KB_Thue(Set<Pair<List<Y>, List<Y>>> rules, int max_iterations) {
		this.rules = rules;
		this.max_iterations = max_iterations;
		orient(this.rules);
	}

	public void complete() {
		go(rules, iteration, max_iterations);
		finished = true;
	}

	/**
	 * DANGEROUS! THIS DOES NOT PROVIDE A TRUE NORMAL FORM!!! ONLY NORMAL WRT LENGTH-PRESERVING EQUATIONS!!
	 *
	 * @param s this parameter is ignore, but required to make sure users read the document to note that this is not a true normal form
	 * @param e the word to normalize
	 * @return the normalized word
	 */
	public List<Y> normalize(String s, List<Y> e) {
		if (!finished) {
			throw new RuntimeException("Must finish completion to obtain normal forms.");
		}
		return normal_form(e, rules);
	}

	public boolean equiv(List<Y> a, List<Y> b) {
//		check_oriented(rules);
		Pair<List<Y>, List<Y>> pair = new Pair<>(a, b);
		if (equivs.containsKey(pair)) {
			return equivs.get(pair);
		}
		boolean eq = almost_joinable(a, b, rules);
		if (finished) {
			equivs.put(pair, eq);
			return eq;
		}
		if (eq) {
			equivs.put(pair, true);
			return true;
		}
		iteration++;
		if (iteration > max_iterations) {
			throw new RuntimeException("Max iterations exceeded: " + max_iterations);
		}
		finished = step(rules);
		return equiv(a, b);
	}

	// ///////////////////////////////////////////////////////////////////////////////////////////

	private static <X> void orient(Pair<List<X>, List<X>> rule) {
		if (rule.second.size() > rule.first.size()) {
			List<X> old_first = rule.first;
			List<X> old_second = rule.second;
			rule.first = old_second;
			rule.second = old_first;
		}
	}

	private static <X> void orient(Set<Pair<List<X>, List<X>>> t) {
		for (Pair<List<X>, List<X>> rule : t) {
			orient(rule);
		}
	}

	private <X> void go(Set<Pair<List<X>, List<X>>> t, int iteration, int max_iterations) {
		while (!step(t)) {
			if (iteration++ > max_iterations) {
				throw new RuntimeException("Max iterations exceeded: " + max_iterations);
			}
		}
	}

	private <X> boolean step(Set<Pair<List<X>, List<X>>> t) {
		orient(t);
		normalize(t);
		Set<Pair<List<X>, List<X>>> ce = cp(t);
		if (!ce.isEmpty()) {
			t.addAll(ce);
			normalize(t);
			ce = cp(t);
			return false;
		} else {
			simplify(t);
			return true;
		}
	}

	private static <X> Pair<List<X>, List<X>> getUnmarked(Set<Pair<List<X>, List<X>>> marked,
			Set<Pair<List<X>, List<X>>> t) {
		for (Pair<List<X>, List<X>> rule : t) {
			if (!marked.contains(rule)) {
				return rule;
			}
		}
		return null;
	}

	private <X> void simplify(Set<Pair<List<X>, List<X>>> t) {
		Iterator<Pair<List<X>, List<X>>> it = t.iterator();
		while (it.hasNext()) {
			Pair<List<X>, List<X>> rule = it.next();
			Set<Pair<List<X>, List<X>>> t0 = new HashSet<>(t);
			t0.remove(rule);
			if (!normal_form(rule.first, t0).equals(rule.first)) {
				it.remove();
				continue;
			}
			// if (!normal_form(rule.second, t0).equals(rule.second)) {
			// throw new RuntimeException();
			// }
		}
	}

	private <X> void normalize(Set<Pair<List<X>, List<X>>> t) {
		Set<Pair<List<X>, List<X>>> marked = new HashSet<>();
		Pair<List<X>, List<X>> lr = null;
		while ((lr = getUnmarked(marked, t)) != null) {
			t.remove(lr);
			List<X> l0 = normal_form(lr.first, t);
			List<X> r0 = normal_form(lr.second, t);
			if (!almost_joinable(l0, r0, t)) {
				Pair<List<X>, List<X>> l0r0 = new Pair<>(l0, r0);
				orient(l0r0);
				t.add(l0r0);
				marked.add(l0r0);
			}
			marked.add(lr); // TODO added, only in paper in some examples
		}
	}

	/* private static <X> void check_oriented(Set<Pair<List<X>, List<X>>> t) {
			return;
		for (Pair<List<X>, List<X>> r : t) {
			if (r.first.size() < r.second.size()) {
				throw new RuntimeException(t.toString());
			}
		}
	} */

	private <X> List<X> normal_form(List<X> e, Set<Pair<List<X>, List<X>>> t) {
		List<X> ret = new LinkedList<>(e);
		for (Pair<List<X>, List<X>> rule : t) {
			if (rule.first.size() == rule.second.size()) {
				continue;
			}
			int i = occurs(ret, rule.first);
			if (i == -1) {
				continue;
			}
			delete(ret, i, rule.first.size());
			add(ret, i, rule.second);
			if (!e.equals(ret)) {
				return normal_form(ret, t);
			}
		}

		return ret;
	}

	private <X> List<X> apply(List<X> e, Pair<List<X>, List<X>> rule) {
		List<X> ret = new LinkedList<>(e);
		int i = occurs(ret, rule.first);
		if (i == -1) {
			return ret;
		}
		delete(ret, i, rule.first.size());
		add(ret, i, rule.second);
		return ret;
	}

	private static <X> void delete(List<X> l, int i, int size) {
		for (int j = 0; j < size; j++) {
			l.remove(i);
		}
	}

	private static <X> void add(List<X> l, int i, List<X> add) {
		for (int j = add.size() - 1; j >= 0; j--) {
			l.add(i, add.get(j));
		}
	}

	private <X> int occurs(List<X> l, List<X> find) {
		for (int i = 0; i <= l.size() - find.size(); i++) {
			if (occursAt(l, find, i)) {
				return i;
			}
		}
		return -1;
	}

	// assumes does not 'run out the end' (prevented by occurs)
	private static <X> boolean occursAt(List<X> l, List<X> find, int i) {
		for (int j = i, k = 0; j < i + find.size(); j++, k++) {
			if (!l.get(j).equals(find.get(k))) {
				return false;
			}
		}
		return true;
	}

	private <X> boolean almost_joinable(List<X> e, List<X> f, Set<Pair<List<X>, List<X>>> t) {
		List<X> e0 = normal_form(e, t);
		List<X> f0 = normal_form(f, t);

		Set<List<X>> e0_closed = close(e0, t);
		return e0_closed.contains(f0);
	}

	private <X> Set<List<X>> close(List<X> e, Set<Pair<List<X>, List<X>>> t) {
		Set<List<X>> init = new HashSet<>();
		init.add(e);

		for (;;) {
			Set<List<X>> next = close1(init, t);
			if (init.equals(next)) {
				return init;
			}
			init = next;
		}
	}

	private <X> Set<List<X>> close1(Set<List<X>> set, Set<Pair<List<X>, List<X>>> t) {
		Set<List<X>> ret = new HashSet<>(set);

		for (List<X> e : set) {
			for (Pair<List<X>, List<X>> rule : t) {
				if (rule.first.size() != rule.second.size()) {
					continue;
				}
				ret.add(apply(e, rule));
				Pair<List<X>, List<X>> rule2 = rule.reverse();
				ret.add(apply(e, rule2));
			}
		}

		return ret;
	}

	private <X> Set<Pair<List<X>, List<X>>> cp(Set<Pair<List<X>, List<X>>> t) {
		// System.out.println("cp " + t);
		Set<Pair<List<X>, List<X>>> ret = new HashSet<>();
		for (Pair<List<X>, List<X>> rule1 : t) {
			for (Pair<List<X>, List<X>> rule2 : t) {
				if (rule1.first.size() == rule1.second.size()
						&& rule2.first.size() == rule2.second.size()) {
					continue;
				}
				Set<Quad<List<X>, List<X>, List<X>, List<X>>> todo = new HashSet<>();
				if (rule1.first.size() == rule1.second.size()) {
					if (rule2.first.size() == rule2.second.size()) {
						throw new RuntimeException();
					} else {
						todo.add(new Quad<>(rule1.first, rule1.second, rule2.first, rule2.second));
						todo.add(new Quad<>(rule1.second, rule1.first, rule2.first, rule2.second));
					}
				} else {
					if (rule2.first.size() == rule2.second.size()) {
						todo.add(new Quad<>(rule1.first, rule1.second, rule2.first, rule2.second));
						todo.add(new Quad<>(rule1.first, rule1.second, rule2.second, rule2.first));
					} else {
						todo.add(new Quad<>(rule1.first, rule1.second, rule2.first, rule2.second));
					}
				}
				for (Quad<List<X>, List<X>, List<X>, List<X>> rule : todo) {
					addCP1(rule.first, rule.second, rule.third, rule.fourth, t, ret);
					addCP2(rule.first, rule.second, rule.third, rule.fourth, t, ret);
				}
			}
		}
		orient(ret);
		return ret;
	}

	// does not include 0 length lists
	private static <X> Set<Pair<List<X>, List<X>>> split(List<X> l) {
		Set<Pair<List<X>, List<X>>> ret = new HashSet<>();
		for (int i = 1; i < l.size(); i++) {
			ret.add(new Pair<>(l.subList(0, i), l.subList(i, l.size())));
		}
		return ret;
	}

	private <X> void addCP1(List<X> li, List<X> ri, List<X> lj, List<X> rj,
			Set<Pair<List<X>, List<X>>> t, Set<Pair<List<X>, List<X>>> ret) {
		for (Pair<List<X>, List<X>> uv : split(li)) {
			for (Pair<List<X>, List<X>> vw : split(lj)) {
				if (!uv.second.equals(vw.first)) {
					continue;
				}
				List<X> urj = new LinkedList<>(uv.first);
				urj.addAll(rj);
				List<X> riw = new LinkedList<>(ri);
				riw.addAll(vw.second);
				if (!almost_joinable(urj, riw, t)) {
					ret.add(new Pair<>(urj, riw));
				}
			}
		}
	}

	private <X> void addCP2(List<X> li, List<X> ri, List<X> lj, List<X> rj,
			Set<Pair<List<X>, List<X>>> t, Set<Pair<List<X>, List<X>>> ret) {
		Set<Integer> uws = middle(li, lj);
		for (Integer i : uws) {
			List<X> u = li.subList(0, i);
			List<X> w = li.subList(i + lj.size(), li.size());

			// List<X> split = new LinkedList<>(u);
			// split.addAll(lj);
			// split.addAll(w);
			// if (!split.equals(li)) {
			// throw new RuntimeException();
			// }

			List<X> urjw = new LinkedList<>(u);
			urjw.addAll(rj);
			urjw.addAll(w);
			if (!almost_joinable(ri, urjw, t)) {
				ret.add(new Pair<>(ri, urjw));
			}
		}
	}

	private static <X> Set<Integer> middle(List<X> l, List<X> find) {
		Set<Integer> ret = new HashSet<>();
		for (int i = 0; i <= l.size() - find.size(); i++) {
			if (occursAt(l, find, i)) {
				ret.add(i);
			}
		}
		return ret;
	}

	private static String sep(Collection<?> c, String sep) {
		return sep(c.iterator(), sep);
	}

	protected static String sep(Iterator<?> c, String sep) {
		String ret = "";
		boolean b = false;
		while (c.hasNext()) {
			Object o = c.next();
			if (b) {
				ret += sep;
			}
			b = true;

			ret += o;
		}
		return ret;
	}

	@Override
	public String toString() {
		Set<String> ret = rules.stream().map(x -> {
			String s1 = sep(x.first, ".");
			String s2 = sep(x.second, ".");
			if (x.first.size() == x.second.size()) {
				return "  " + s1 + " = " + s2;
			}
			return "  " + s1 + " -> " + s2;
		}).collect(Collectors.toSet());
		return sep(ret, "\n");
	}

}
