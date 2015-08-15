
public class BoundingBox {
	private float x;
	private float y;
	private float z;
	private float l;
	private float b;
	private float h;
	
	public BoundingBox(float x, float y, float z, float l, float b, float h) {
		this.x = x;
		this.y = y;
		this.z = z;
		this.l = l;
		this.b = b;
		this.h = h;
	}
	
	public Point getPos() {
		return new Point(x,y,z);
	}
	
	public Point getSize() {
		return new Point(l,h,b);
	}
	
	public boolean collide(BoundingBox bb) {
		float mx = x + l/2;
		float my = y + h/2;
		float mz = z + b/2;
		float bx = bb.x + (bb.l / 2);
		float by = bb.y + (bb.h / 2);
		float bz = bb.z + (bb.b / 2);
		
		if (bx > x - l/2 && bb.x - bb.l/2 < mx) {
			if (by > y - h/2 && bb.y - bb.h/2 < my) {
				if (bz > z - b/2 && bb.z - bb.b/2 < mz) {
					return true;
				}
			}
		}
		
		return false;
	}
}
