package basic;

public class Pair<F, S> {
	
	private F f;
	private S s;
	
	public Pair(F f, S s) {
		this.f = f;
		this.s = s;
	}

	public F getF() {
		return f;
	}
	
	public S getS() {
		return s;
	}

}
