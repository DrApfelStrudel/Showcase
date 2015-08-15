
public class Camera {
	
	private float x;
	private float y;
	private float z;
	public float l = 0.5f;
	public float b = 0.5f;
	public float h = 1f;
	private float rotX = 0;
	private float rotY = 0;
	private float rotZ = 0;
	public BoundingBox bounds;

	public Camera(float x, float y, float z) {
		this.x = x;
		this.y = y;
		this.z = z;
	}
	
	public Point pos() {
		return new Point(x,y,z);
	}
	
	public void update() {
		bounds = new BoundingBox(x, y, z, l, b, h);
	}
	
	public void setX(float i) {
		x = i;
		update();
	}
	
	public void setY(float i) {
		y = i;
		update();
	}
	
	public void setZ(float i) {
		z = i;
		update();
	}
	
	public void setPos(Point p, float a, float b, float c) {
		x = p.x + a;
		y = p.y + c;
		z = p.z + b;
		update();
	}
	
	public void setRotX(float i) {
		rotX = i;
	}
	
	public void setRotY(float i) {
		rotY = i;
	}
	
	public void setRotZ(float i) {
		rotZ = i;
	}
	
	public float getX() {
		return x;
	}
	
	public float getY() {
		return y;
	}
	
	public float getZ() {
		return z;
	}
	
	public float getRotX() {
		return rotX;
	}
	
	public float getRotY() {
		return rotY;
	}
	
	public float getRotZ() {
		return rotZ;
	}
}
