import org.newdawn.slick.opengl.Texture;


public class MovingCube extends Cube3D {
	
	Point vector;
	Point point;
	private Point p1;
	private Point p2;
	private Point v1;
	private Point v2;
	private float speed = 0.05f;

	public MovingCube(float x, float y, float z, float l, float b, float h, Point color, Texture tex, Point p1, Point p2) {
		super(x, y, z, l, b, h, color, tex);

		float diffX = p1.x - p2.x;
		float diffY = p1.y - p2.y;
		float diffZ = p1.z - p2.z;
		
		float k = (diffX*diffX) + (diffY*diffY) + (diffZ*diffZ);

		diffX = (float) ((diffX) / Math.sqrt(k)) * speed;
		diffY = (float) ((diffY) / Math.sqrt(k)) * speed;
		diffZ = (float) ((diffZ) / Math.sqrt(k)) * speed;
		
		v1 = new Point(diffX, diffY, diffZ);
		v2 = new Point(-diffX, -diffY, - diffZ);
		this.p1 = p1;
		this.p2 = p2;
		vector = v1;
		point = p1;
	}
	
	public void move() {
		if (x < point.x+0.3f && x > point.x-0.3f && z < point.z+0.3f && z > point.z-0.3f) {
			if (vector == v1 && point == p1) {
				vector = v2; point = p2;
			}
			else {
				vector = v1; point = p1;
			}
		}

		x += vector.x;
		y += vector.y;
		z += vector.z;
		h += 0.1f;
		update();
		for (Entity e : GameBoard.entities) {
			if (bounds.collide(e.bounds)) {
				e.x += vector.x;
				e.y += vector.y;
				e.z += vector.z;
				for (Cube3D c : Data.cubes) {
					if (c != this && (c.y + c.h/2 - 0.1f) > (e.y - e.boundPoints.y/2)) {
						if (c.bounds.collide(e.bounds)) {
							e.health = 0;
						}
					}
				}
				if (e instanceof Player) {
					((Player) e).updateCam();
				}
			}
		}

		h -= 0.1f;
		update();
	}

}
