package basic;

public class Vector {
	private float x, y;
	
	public Vector(float newX, float newY) {
		setX(newX);
		setY(newY);
	}

	public float getX() {
		return x;
	}

	public void setX(float x) {
		this.x = x;
	}

	public float getY() {
		return y;
	}

	public void setY(float y) {
		this.y = y;
	}
	
	public void addVector(Vector o) {
		x = x + o.getX();
		y = y + o.getY();
	}
	
	public Vector mulVector(float k) {
		return new Vector(x * k, y * k);
	}
	
	public float length() {
		return (float) Math.sqrt(x * x + y * y);
	}
	
	public Vector unitVector() {
		return new Vector((float) (x / Math.sqrt(x*x+y*y)), (float) (y / Math.sqrt(x*x+y*y)));
	}
	
	public float angle() {
		Vector unit = unitVector();
		return x == 0 && y == 0 ? 0 : unit.y < 0 ? 
				360 - (float) Math.toDegrees(Math.acos(unit.x)):
				(float) Math.toDegrees(Math.acos(unit.x)); 
	}
	
	public String toString() {
		return "Vector[" + x + "," + y + "]";
	}
}
