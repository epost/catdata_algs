package catdata.algs;

/**
 * @author Ryan Wisnesky
 */
public class Chc<X,Y> {
	public Boolean left;
	
	public X l;
	public Y r;
	
	public static <X,Y> Chc<X,Y> inLeft(X l) {
		Chc<X,Y> ret = new Chc<>();
		ret.left = true;
		ret.l = l;
		return ret;
	}
	
	public static <X,Y> Chc<X,Y> inRight(Y r) {
		Chc<X,Y> ret = new Chc<>();
		ret.left = false;
		ret.r = r;
		return ret;
	}

	public String toString() {
		if (left) {
			return "inl " + l;
		} else {
			return "inr " + r;
		}
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((l == null) ? 0 : l.hashCode());
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((r == null) ? 0 : r.hashCode());
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
		Chc<?,?> other = (Chc<?,?>) obj;
		if (l == null) {
			if (other.l != null)
				return false;
		} else if (!l.equals(other.l))
			return false;
		if (left == null) {
			if (other.left != null)
				return false;
		} else if (!left.equals(other.left))
			return false;
		if (r == null) {
			if (other.r != null)
				return false;
		} else if (!r.equals(other.r))
			return false;
		return true;
	}
	
}