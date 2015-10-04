package catdata.algs.kb;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import catdata.algs.Triple;

/**
 * 
 * @author Ryan Wisnesky
 *
 * First-order terms with constants/functions, and variables.
 *
 * @param <C> type of constant/function symbols
 * @param <V> type of variables
 */
public abstract class KBExp<C, V> {

	public static interface KBExpVisitor<C, V, R, E> {
		public R visit(E env, KBVar<C, V> e);
		public R visit(E env, KBApp<C, V> e);
	}

	@Override
	public abstract boolean equals(Object o);

	@Override
	public abstract int hashCode();

	public abstract <R, E> R accept(E env, KBExpVisitor<C, V, R, E> e);

	public abstract boolean hasAsSubterm(KBExp<C, V> sub);

	public abstract boolean occurs(V v);

	public abstract KBExp<C, V> subst(Map<V, KBExp<C, V>> sigma);

	protected abstract void vars(Set<V> vars);

	public abstract Set<Triple<KBExp<C, V>, KBExp<C, V>, Map<V, KBExp<C, V>>>> cp(List<Integer> l,
			KBExp<C, V> a, KBExp<C, V> b, KBExp<C, V> g, KBExp<C, V> d);

	public abstract KBExp<C, V> replace(List<Integer> p, KBExp<C, V> r);

	public abstract KBExp<C, V> freeze();

	public abstract KBExp<C, V> unfreeze();

	public boolean isVar;

	public abstract KBVar<C, V> getVar();

	public abstract KBApp<C, V> getApp();

	private Set<V> vars = null;

	public Set<V> vars() {
		if (vars == null) {
			vars = new HashSet<>();
			vars(vars);
		}
		return vars;
	}

	// //////////////////////////////////////////////////////////////////////////////////////////////////

	public static class KBVar<C, V> extends KBExp<C, V> {
		public V var;

		public KBVar(V var) {
			this.var = var;
			isVar = true;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((var == null) ? 0 : var.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			KBVar<?, ?> other = (KBVar<?, ?>) obj;
			if (var == null) {
				if (other.var != null)
					return false;
			} else if (!var.equals(other.var))
				return false;
			return true;
		}

		@Override
		public String toString() {
			return var.toString();
		}

		@Override
		public <R, E> R accept(E env, KBExpVisitor<C, V, R, E> v) {
			return v.visit(env, this);
		}

		@Override
		public boolean occurs(V v) {
			return var.equals(v);
		}

		@Override
		public KBExp<C, V> subst(Map<V, KBExp<C, V>> sigma) {
			KBExp<C, V> ret = sigma.get(var);
			if (ret == null) {
				return this;
			}
			return ret;
		}

		@Override
		public Set<Triple<KBExp<C, V>, KBExp<C, V>, Map<V, KBExp<C, V>>>> cp(List<Integer> l,
				KBExp<C, V> a, KBExp<C, V> b, KBExp<C, V> g, KBExp<C, V> d) {
			return new HashSet<>();
		}

		@Override
		public KBExp<C, V> replace(List<Integer> l, KBExp<C, V> r) {
			if (l.isEmpty()) {
				return r;
			}
			throw new RuntimeException("Cannot replace");
		}

		KBExp<C, V> frozen = null;

		@SuppressWarnings({ "unchecked", "rawtypes" })
		@Override
		public KBExp<C, V> freeze() {
			if (frozen == null) {
				frozen = new KBApp(this, new LinkedList<>()); // note violation
																// of
																// type-safety
			}
			return frozen;
		}

		@Override
		public KBExp<C, V> unfreeze() {
			throw new RuntimeException();
		}

		@Override
		public boolean hasAsSubterm(KBExp<C, V> sub) {
			return this.equals(sub);
		}

		@Override
		public void vars(Set<V> vars) {
			vars.add(var);
		}

		@Override
		public KBVar<C, V> getVar() {
			return this;
		}

		@Override
		public KBApp<C, V> getApp() {
			throw new RuntimeException();
		}

	}

	// //////////////////////////////////////////////////////////////////////////////////////////////////

	public static class KBApp<C, V> extends KBExp<C, V> {
		public C f;
		public List<KBExp<C, V>> args;

		public KBApp(C f, List<KBExp<C, V>> args) {
			this.f = f;
			this.args = args;
			isVar = false;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((args == null) ? 0 : args.hashCode());
			result = prime * result + ((f == null) ? 0 : f.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			KBApp<?, ?> other = (KBApp<?, ?>) obj;
			if (args == null) {
				if (other.args != null)
					return false;
			} else if (!args.equals(other.args))
				return false;
			if (f == null) {
				if (other.f != null)
					return false;
			} else if (!f.equals(other.f))
				return false;
			return true;
		}

		@Override
		public String toString() {
			if (args.isEmpty()) {
				return f.toString();
			}
			if (args.size() == 2) {
				return "(" + args.get(0) + " " + f + " " + args.get(1) + ")";
			}
			if (args.size() == 1 && !args.get(0).isVar && args.get(0).getApp().args.size() == 2) {
				return f + KB.sep(args, ",");
			}
			return f + "(" + KB.sep(args, ",") + ")";
		}

		@Override
		public <R, E> R accept(E env, KBExpVisitor<C, V, R, E> v) {
			return v.visit(env, this);
		}

		@Override
		public boolean occurs(V v) {
			for (KBExp<C, V> arg : args) {
				if (arg.occurs(v)) {
					return true;
				}
			}
			return false;
		}

		@Override
		public KBExp<C, V> subst(Map<V, KBExp<C, V>> sigma) {
			List<KBExp<C, V>> n = new LinkedList<>();
			for (KBExp<C, V> arg : args) {
				n.add(arg.subst(sigma));
			}
			return new KBApp<>(f, n);
		}

		@Override
		public void vars(Set<V> vars) {
			for (KBExp<C, V> e : args) {
				e.vars(vars);
			}
		}

		@Override
		public Set<Triple<KBExp<C, V>, KBExp<C, V>, Map<V, KBExp<C, V>>>> cp(List<Integer> p,
				KBExp<C, V> a, KBExp<C, V> b, KBExp<C, V> g, KBExp<C, V> d) {
			Set<Triple<KBExp<C, V>, KBExp<C, V>, Map<V, KBExp<C, V>>>> ret = new HashSet<>();
			int q = 0;
			for (KBExp<C, V> arg : args) {
				List<Integer> p0 = new LinkedList<>(p);
				p0.add(q++);
				ret.addAll(arg.cp(p0, a, b, g, d));
			}

			Map<V, KBExp<C, V>> s = KBUnifier.unify0(this, a);
			if (s != null) {
				Triple<KBExp<C, V>, KBExp<C, V>, Map<V, KBExp<C, V>>> toadd = new Triple<>(
						d.subst(s), g.replace(p, b).subst(s), s);
				ret.add(toadd);
			}
			return ret;
		}

		@Override
		public KBExp<C, V> replace(List<Integer> l, KBExp<C, V> r) {
			if (l.isEmpty()) {
				return r;
			}
			Integer x = l.get(0);
			List<KBExp<C, V>> new_args = new LinkedList<>();
			for (int i = 0; i < args.size(); i++) {
				KBExp<C, V> a = args.get(i);
				if (i == x) {
					a = a.replace(l.subList(1, l.size()), r);
				}
				new_args.add(a);
			}
			return new KBApp<>(f, new_args);
		}

		KBExp<C, V> freeze = null;

		@Override
		public KBExp<C, V> freeze() {
			if (freeze == null) {
				List<KBExp<C, V>> new_args = new LinkedList<>();
				for (KBExp<C, V> arg : args) {
					new_args.add(arg.freeze());
				}
				freeze = new KBApp<>(f, new_args);
			}
			return freeze;
		}

		KBExp<C, V> unfreeze = null;

		@SuppressWarnings("unchecked")
		@Override
		public KBExp<C, V> unfreeze() {
			if (unfreeze == null) {
				if (f instanceof KBVar) {
					unfreeze = (KBVar<C, V>) f;
				} else {
					List<KBExp<C, V>> new_args = new LinkedList<>();
					for (KBExp<C, V> arg : args) {
						new_args.add(arg.unfreeze());
					}
					unfreeze = new KBApp<C, V>(f, new_args);
				}
			}
			return unfreeze;
		}

		@Override
		public boolean hasAsSubterm(KBExp<C, V> sub) {
			if (this.equals(sub)) {
				return true;
			}
			for (KBExp<C, V> arg : args) {
				if (arg.hasAsSubterm(sub)) {
					return true;
				}
			}
			return false;
		}

		@Override
		public catdata.algs.kb.KBExp.KBVar<C, V> getVar() {
			throw new RuntimeException();
		}

		@Override
		public KBApp<C, V> getApp() {
			return this;
		}
	}

}
