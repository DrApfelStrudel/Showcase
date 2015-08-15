import org.lwjgl.opengl.GL11;
import org.lwjgl.util.vector.Vector3f;

public class Help {
	public static float dist(Vector3f v) {
		return (float) Math.sqrt((v.x*v.x)+(v.y*v.y)+(v.z*v.z));
	}
	
	private static float r = 0.4f, g = 0.4f, b = 0.4f;
	private static boolean[] d = new boolean[3];
	private static int timer = 0;
	
	public static Point shiftingColor() {
		if (timer % 10000 == 0) {
		if (d[0]) r += 0.01f;
		else 	  r -= 0.01f;
		if (!d[1]) g += 0.01f;
		else	  g -= 0.01f;
		if (d[2]) b += 0.01f;
		else	  b -= 0.01f;
		
		if (r < 0.33f || r > 0.66f) d[0] = !d[0];
		if (r < 0.33f || r > 0.66f) d[1] = !d[1];
		if (r < 0.33f || r > 0.66f) d[2] = !d[2];
		}
		
		timer++;
		
		return new Point(r,g,b);
	}
	
	public static Vector3f vectorCenter(float speed, float x, float y, float z) {
		Vector3f v = new Vector3f(-x,-y,-z);
		float c = speed/dist(v);
		v.x *= c;
		v.y *= c;
		v.z *= c;
		return v;
	}
	
	public static Vector3f vectorToPoint(float speed, float x, float y, float z, float x0, float y0, float z0) {
		Vector3f v = new Vector3f(x0-x,y0-y,z0-z);
		float c = speed/dist(v);
		v.x *= c;
		v.y *= c;
		v.z *= c;
		return v;
	}
	
	public static void drawCircle(int vertices, float x, float y, float z, float maxSize, Point color) {
		float verticeAngle = 360/vertices;
		
		GL11.glBegin(GL11.GL_TRIANGLES);
		
		for (int i = 0; i < 360; i += verticeAngle) {
		GL11.glColor3f(color.x, color.y, color.z);
		GL11.glVertex3f((float) (x + (maxSize/2)*Math.cos(Math.toRadians(i))), y, (float)(z + (maxSize/2)*Math.sin(Math.toRadians(i))));
		GL11.glColor3f(color.x, color.y, color.z+0.1f);
		GL11.glVertex3f(x, y, z);
		GL11.glColor3f(color.x, color.y+0.1f, color.z);
		GL11.glVertex3f((float) (x + (maxSize/2)*Math.cos(Math.toRadians(i+verticeAngle))), y, (float)(z + (maxSize/2)*Math.sin(Math.toRadians(i+verticeAngle))));
		}
		
		GL11.glEnd();
	}
}
