package catdata.algs.kb;

import java.util.function.Function;

import catdata.algs.Pair;
import catdata.algs.kb.KBExp.KBApp;

/**
 * 
 * @author Ryan Wisnesky
 *
 * Class for term orderings.  Only contains one, lexicographic path ordering left to right.
 */
public class KBOrders {
	
	public static <C, V> Function<Pair<KBExp<C, V>, KBExp<C, V>>, Boolean> lpogt(
			Function<Pair<C, C>, Boolean> gt) {
		return new Function<Pair<KBExp<C, V>, KBExp<C, V>>, Boolean>() {
			@Override
			public Boolean apply(Pair<KBExp<C, V>, KBExp<C, V>> xxx) {
				
				KBExp<C, V> s = xxx.first;
				KBExp<C, V> t = xxx.second;

				//http://resources.mpi-inf.mpg.de/departments/rg1/teaching/autrea-ss10/script/lecture20.pdf
				
				//LPO1
				if (t.isVar) {
					return !t.equals(s) && s.vars().contains(t.getVar().var);
				}
				if (s.isVar) {
					//TODO: KB will fail on var = const
					//if (DEBUG.debug.opl_david) {
						//if (t.vars().isEmpty()) {
							//return true;
						//}
					//}
					return false;
				} 

				//LPO2
				KBApp<C, V> s0 = s.getApp();
				KBApp<C, V> t0 = t.getApp();
				C f = s0.f;
				C g = t0.f;

				//LPO2a
				for (KBExp<C, V> si : s0.args) {
					if (apply(new Pair<>(si, t)) || si.equals(t)) {
						return true;
					}
				}

				//LPO2b
				if (gt.apply(new Pair<>(f, g))) { 
					for (KBExp<C, V> ti : t0.args) {
						if (!apply(new Pair<>(s, ti))) {
							return false;
						}
					}
					return true;
				} 
				
				//LPO2c
				if (f.equals(g)) {
					for (KBExp<C, V> ti : t0.args) {
						if (!this.apply(new Pair<>(s0, ti))) {
							return false;
						}
					}
					int i = 0;
					for (KBExp<C, V> si : s0.args) {
						if (i > t0.args.size()) {
							return false;
						}
						KBExp<C, V> ti = t0.args.get(i++);
						if (this.apply(new Pair<>(si, ti))) {
							return true;
						}
						if (this.apply(new Pair<>(ti, si))) {
							return false;
						}
						if (si.equals(ti)) {
							continue;
						}
						return false;
					}
				}
				return false;
			}
		};
	}

	
}
