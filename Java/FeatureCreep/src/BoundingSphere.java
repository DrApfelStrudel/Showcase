import org.lwjgl.util.vector.Vector3f;

public class BoundingSphere {
	public float x, y, z, radius;
	
	public BoundingSphere(float x, float y, float z, float radius) {
		this.x = x;
		this.y = y;
		this.z = z;
		this.radius = radius;
	}
	
	public boolean collidesWith(BoundingSphere b) {
		Vector3f distV = new Vector3f(b.x-x,b.y-y,b.z-z);
		float dist = Help.dist(distV) - b.radius - radius;
		return dist <= 0;
	}
}
