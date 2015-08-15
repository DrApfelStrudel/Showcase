package basic;

import org.newdawn.slick.Color;

public class Light {
	
	private float radius;
	private Entity e;

	public Light(Entity e, float radius) {
		this.e = e;
		this.radius = radius;
	}
	
	public void lightUp() {
		Util.drawGradientCircle(getX(), getY(), 40, radius, Color.white);
	}

	public String toString() {
		return "Light["+getX()+","+getY()+","+radius+"]";
	}
	
	public void setRadius(float newRadius) {
		radius = newRadius;
	}
	
	public float getX() {
		return e.getX();
	}
	
	public float getY() {
		return e.getY();
	}

	public float getRadius() {
		return radius;
	}
}
