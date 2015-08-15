import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;


public class Util {
	public static float distanceFrom(Point a, Point b) {
		return (float)Math.sqrt((a.x-b.x)*(a.x-b.x)+(a.y-b.y)*(a.y-b.y)+(a.z-b.z)*(a.z-b.z));
	}
	
	public static Tile toTile(Point p) {
		return new Tile((int)Math.round((p.x)/0.25f), (int)Math.round(((p.y)/0.25f)), (int)Math.round(((p.z)/0.25f)));
	}
	
	public static Point toPos(Point p) {
		return new Point((p.x) * 0.25f - 0.125f, (p.y) * 0.25f + 0.125f, (p.z) * 0.25f - 0.125f);
	}
	
	public static int degreeBetween(Point a, Point b) {
		double distX = b.x - a.x;
		double distZ = b.z - a.z;

		double factor = Math.sqrt((distX)*(distX) + (distZ)*(distZ));
		
		int degree = ((int) Math.round(Math.toDegrees(Math.acos(distX/factor))));
		
		if (distZ < 0) {
			degree = 360 - degree;
		}
		
		return 360 - degree;
	}
	
	public static float dotP(Point a, Point b) {
		return (a.x*b.x) + (a.y*b.y) + (a.z*b.z);
	}
	
	public static float length(Point a) {
		return (float) Math.sqrt((a.x*a.x)+(a.y*a.y)+(a.z*a.z));
	}
	
	public static int degreeYBetween(Point a, Point b) {
		float distX = b.x - a.x;
		float distY = b.y - a.y;
		float distZ = b.z - a.z;

		Point vector = new Point(distX, distY, distZ);
		Point vector2 = new Point(distX, 0, distZ);
		
		float sum1 = dotP(vector,vector2) / (length(vector) * length(vector2));

		int degree = (int) Math.toDegrees((Math.acos(sum1)));
		
		if (distY >= 0) {
			degree = -degree;
		}
		
		return degree;
	}
	
	public static float degreeDiff(float a, float b) {
		if (Math.abs(a-b) >= 180) {
			return (360-Math.max(a, b)) + Math.min(a, b); 
		}
		else {
			return Math.abs(a-b);
		}
	}

	public static int numberAt(String s, int pos) {
		int current = 1;
		String retur = "";
		for (int i = 2; i < s.length(); i++) {
			if (!(s.charAt(i) == ',') && !(s.charAt(i) == ')')) {
				retur += s.charAt(i);
			}
			else {
				if (current == pos) {
					return Integer.parseInt(retur);
				}
				else {
					retur = "";
					current++;
				}
			}
		}
		return -1;
	}
	
	public static void loadLevel(String url) {
		try {
			BufferedReader in = new BufferedReader(new FileReader(url));
			String line;
			while((line = in.readLine()) != null)
			{
				if (line.charAt(0) == 'c') {
					Cube3D c = new Cube3D(numberAt(line,1),numberAt(line,2),numberAt(line,3),numberAt(line,4),numberAt(line,5),numberAt(line,6), new Point(1,1,1), TexLoad.tex[numberAt(line,8)]);
			    	c.update();
					Data.cubes.add(c);
				}
			}
		} catch (FileNotFoundException e) {
			System.exit(0);
			e.printStackTrace();
		} catch (IOException e) {
			System.exit(0);
			e.printStackTrace();
		}
	}
}
