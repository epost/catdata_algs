package catdata.algs.kb;

import java.util.HashMap;
import java.util.Map;

import catdata.algs.kb.KBExp.KBApp;

/**
 * 
 * @author Ryan Wisnesky
 *
 * Naive implementation of first-order unification.
 *
 * @param <C> type of constant/function symbols
 * @param <V> type of variables
 */
public class KBUnifier<C, V> {

	public static <C, V> Map<V, KBExp<C, V>> findSubst(KBExp<C, V> s, KBExp<C, V> t) {
		// if (!Collections.disjoint(s.vars_fast(), t.vars_fast())) {
		// throw new RuntimeException("not disjoint in findsubst");
		// }
		Map<V, KBExp<C, V>> m = unify0(s, t.freeze());
		if (m == null) {
			return null;
		}
		Map<V, KBExp<C, V>> ret = new HashMap<>();
		for (V v : m.keySet()) {
			ret.put(v, m.get(v).unfreeze());
		}
		return ret;
	}

	public static <C, V> Map<V, KBExp<C, V>> unify0(KBExp<C, V> s, KBExp<C, V> t) {
		if (s.isVar) {
			V v = s.getVar().var;
			if (!t.isVar && t.vars().contains(v)) {
				return null; // occurs check failed
			}
			return singleton(v, t);
		}
		KBApp<C, V> s0 = (KBApp<C, V>) s;
		if (t.isVar) {
			V v = t.getVar().var;
			if (s.vars().contains(v)) {
				return null; // occurs check failed
			}
			return singleton(v, s);
		}
		KBApp<C, V> t0 = t.getApp();
		if (!s0.f.equals(t0.f)) {
			return null;
		}
		if (s0.args.size() != t0.args.size()) {
			return null;
		}
		Map<V, KBExp<C, V>> ret = new HashMap<>();
		for (int i = 0; i < s0.args.size(); i++) {
			Map<V, KBExp<C, V>> m = unify0(s0.args.get(i).subst(ret), t0.args.get(i).subst(ret));
			if (m == null) {
				return null;
			}
			ret = andThen(ret, m);
		}
		// if (ret != null && !s.subst(ret).equals(t.subst(ret))) {
		// throw new RuntimeException("trying to unify " + s + " and " + t +
		// " yields " + ret + " but " + s.subst(ret) + " and " + t.subst(ret));
		// }
		return ret;
	}

	private static <C, V> Map<V, KBExp<C, V>> singleton(V v, KBExp<C, V> t) {
		Map<V, KBExp<C, V>> ret = new HashMap<>();
		ret.put(v, t);
		return ret;
	}

	private static <C, V> Map<V, KBExp<C, V>> andThen(Map<V, KBExp<C, V>> s, Map<V, KBExp<C, V>> t) {
		Map<V, KBExp<C, V>> ret = new HashMap<>();

		for (V k : s.keySet()) {
			ret.put(k, s.get(k).subst(t));
		}
		for (V k : t.keySet()) {
			if (!s.containsKey(k)) {
				ret.put(k, t.get(k));
			}
		}

		return ret;
	}

}
