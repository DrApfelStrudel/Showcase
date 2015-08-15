import java.util.HashMap;

import org.lwjgl.input.Mouse;
import org.lwjgl.opengl.Display;
import org.lwjgl.opengl.GL11;


public class Player extends Entity {
	
	private Camera cam;
	private boolean activated = true;
	public static HashMap<String, Boolean> key;
	
	public Player(float x, float y, float z) {
		super(x,y,z, 100);
		cam = new Camera(x,y,z);
		cam.setRotX(80);
		key = new HashMap<String, Boolean>();
		key.put("w", false);
		key.put("a", false);
		key.put("d", false);
		key.put("s", false);
		key.put("k", false);
		key.put("space", false);
		key.put("lshift", false);
		key.put("esc", false);
		key.put("1", false);
		key.put("2", false);
		boundPoints = new Point(0.6f, 0.6f, 1);
		dieSound = Data.audio[16];
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
	}
	
	public void setColor(Point c) {
		color = c;
	}
	
	public Camera getCam() {
		return cam;
	}
	
	public boolean canSee(Point p) {

		BoundingBox current = new BoundingBox(getPos().x, getPos().y + 0.75f, getPos().z, 0.00125f, 0.00125f, 0.00125f);
		BoundingBox target = new BoundingBox(p.x,p.y,p.z, 1,1,1);
		
		this.p = p;
		
		int degree = Util.degreeBetween(p, getPos());
		float pla = (360 - getCam().getRotY()%360 - 90)%360;
		float deg = Util.degreeDiff(degree, pla);
		
		int degree2 = Util.degreeYBetween(p, getPos());
		float pla2 = getCam().getRotX()*-1;
		float deg2 = Util.degreeDiff(degree2, pla2);
		
		float reach = 50;

		float diffX = p.x - current.getPos().x;
		float diffY = p.y - current.getPos().y;
		float diffZ = p.z - current.getPos().z;
		
		float k = (diffX*diffX) + (diffY*diffY) + (diffZ*diffZ);

		diffX = (float) ((diffX) / Math.sqrt(k)) / 8;
		diffY = (float) ((diffY) / Math.sqrt(k)) / 8;
		diffZ = (float) ((diffZ) / Math.sqrt(k)) / 8;
		
		Point diffVector = new Point(diffX, diffY, diffZ);
		
		while (!current.collide(target)) {

			current = new BoundingBox(current.getPos().x + diffVector.x, current.getPos().y + diffVector.y, current.getPos().z + diffVector.z, 0.000125f, 0.000125f, 0.000125f);

			for (Cube3D cu : Data.cubes) {
				if (current.collide(cu.bounds)) {
					return false;
				}
			}
			
		}
		return deg <= reach && deg2 <= reach;
	}
	
	Point p = new Point(1,2,3);

	Point help = new Point(1,1,1);
	
	@Override
	public void Render() {
		Cube3D body = new Cube3D(0,-0.1f,0,0.2f,0.5f,0.1f,color, TexLoad.tex[1]);
		Cube3D head = new Cube3D(0,0.25f,0,0.2f,0.25f,0.2f,color, TexLoad.tex[1]);
		Cube3D face = new Cube3D(0,0.25f,-0.1005f,0.15f,0.20f,0,new Point(1,1,1), TexLoad.tex[5]);
		Cube3D left = new Cube3D(-0.125f,-0.05f,0,0.05f,0.35f,0.05f,color, TexLoad.tex[1]);
		Cube3D right = new Cube3D(0.125f,-0.05f,0,0.05f,0.35f,0.05f,color, TexLoad.tex[1]);
		body.setTexBound(new Point(1,1,1));
		head.setTexBound(new Point(1,1,1));
		left.setTexBound(new Point(1,1,1));
		right.setTexBound(new Point(1,1,1));
		face.setTexBound(new Point(1,1,1));
		face.toggleRemoveBack();
		GL11.glPushMatrix();
		GL11.glTranslatef(x, y, z);
		//GL11.glTranslatef(0, 2f, 0);
		GL11.glRotatef(-cam.getRotY(), 0, 1, 0);
		body.draw();
		GL11.glPushMatrix();
		GL11.glTranslatef(0,0.125f, 0);
		GL11.glRotatef(-cam.getRotX(), 1, 0, 0);
		GL11.glTranslatef(0,-0.125f,0);
		head.draw();
		face.draw();
		GL11.glPopMatrix();
		GL11.glPushMatrix();
		GL11.glTranslatef(0.175f, 0.1f, 0);
		GL11.glRotatef(-cam.getRotX()+90 , 1, 0, 0);
		GL11.glTranslatef(-0.175f, -0.1f, 0);
		left.draw();
		right.draw();
		GL11.glPopMatrix();
		GL11.glPopMatrix();
	}

	@Override
	public void Update() {
		health -= 0.01f;
		OriginalColor = new Point(0.05f, (100-health)/100f, 0.05f);
		keyEvents();
		if (key.get("1")) {
			weapon = 1;
		}
		else if (key.get("2")) {
			weapon = 2;
		}
	}
	
	public Point pos() {
		return new Point(x,y,z);
	}
	
	public void setPos(Point p) {
		x = p.x;
		y = p.y;
		z = p.z;
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
	}
	
	public void toggle() {
		activated = !activated;
		Mouse.setGrabbed(!Mouse.isGrabbed());
	}
	
	public float calc(float f) {
		return Math.round(f*4)/4f;
	}
	
	public void updateBounds() {
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
	}
	
	private int shootCD = 0;
	private int weapon = 1;
	
	public void keyEvents() {
		mouseMove();
		falling = true;
		Point before = pos();
		float b = (float) (Math.cos(Math.toRadians(cam.getRotY()))*speed);
		float a = (float) (Math.sin(Math.toRadians(cam.getRotY()))*speed);

		//if (Mouse.isButtonDown(0)) {
		//	Data.cubes.add(new Cube3D(setX, setY+0.125f, setZ,0.25f,0.25f,0.25f,new Point(0.75f,0f,0.6f), TexLoad.tex[7]));
		//}

	    if (key.get("w")) {
			z = (z - b);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {			
					z = z + b;
					break;	
				}
			} 
			x = (x + a);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					x = x - a;
					break;
				}
			} 
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			before = pos();
		}
		
		if (key.get("s")) {
			z = (z + b);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					z = z - b;
					break;
				}
			} 
			x = (x - a);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					x = x + a;
					break;
				}
			} 
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			before = pos();
		}
		
		if (key.get("d")) {
			z = (z + a);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					z = z - a;
					break;
				}
			} 
			x = (x + b);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					x = x - b;
					break;
				}
			} 
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			before = pos();
		}
		
		if (key.get("a")) {
			z = (z - a);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					z = z + a;
					break;
				}
			} 
			x = (x - b);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					x = x + b;
					break;
				}
			} 
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
			before = pos();
		}

		if (downspeed > 1) {
			downspeed = 1f;
		}
		y = (y - 0.00001f - downspeed);
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		
		SPACE : for (Cube3D c : Data.cubes) {
				if (bounds.collide(c.bounds)) {
					if (c.bounds.getPos().y < y) {
						y = (c.bounds.getPos().y + c.bounds.getSize().y/2 + bounds.getSize().y/2);
						bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
						falling = false;
						knockVector = new Point(knockVector.x, 0, knockVector.z);
						if (downspeed > 0.3f) {
							isHit = true;
							health -= (downspeed - 0.3f) * 100;
						}
						noJump = false;
						downspeed = 0;
						jumping = false;
						break SPACE;
					}
					else {
						jumping = false;
						noJump = true;
					}
				}
			}
		
		if (key.get("space")) {
			if (!noJump) {
				Data.audio[2].playAsSoundEffect(1, 0.9f, false);
				noJump = true;
				jumping = true;
			}
		}
		
		if (falling) {
			setPos(before);
			y = (y - (downspeed += gravity));
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		}
		
		JUMP : for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {
				jumping = false;
				break JUMP;
			}
		}
		
		if (jumping) {
			y = (y + jumpPower);
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		}
		
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		
		updateCam();
		
		if (weapon == 1) {
			if (shootCD++ > LifeDrain.cd && Mouse.isButtonDown(0)) {
				GameBoard.entities.add(new LifeDrain(cam.getX(),cam.getY(),cam.getZ(),-cam.getRotY(), -cam.getRotX(),this));
				shootCD = 0;
			}
		}
		if (weapon == 2) {
			if (shootCD++ > Blast.cd && Mouse.isButtonDown(0)) {
				GameBoard.entities.add(new Blast(cam.getX(),cam.getY(),cam.getZ(),-cam.getRotY(), -cam.getRotX(),this));
				shootCD = 0;
			}
		}

	}
	
	public void updateCam() {
		float b = (float) (Math.cos(Math.toRadians(cam.getRotY()))*speed);
		float a = (float) (Math.sin(Math.toRadians(cam.getRotY()))*speed);
		float ce = (float) (Math.cos(Math.toRadians(-cam.getRotX())));

		b = b / speed * 0.05f;
		a = a / speed * 0.05f;

		float var1 = (a)*(ce/2)+2f*a;
		float var2 = (-b)*(ce/2)-2f*b;
		float var3 = ce/40+0.2f;
		
		cam.setPos(pos(), var1, var2, var3);
	}
	
	
	private int DX = Mouse.getX();
	private int DY = Mouse.getY();
	private int mouseTimer = 0;

	public void mouseMove() {
					DX -= Mouse.getX();
					DY -= Mouse.getY();
					cam.setRotY((cam.getRotY() - DX) % 360);
					int mouseDY = -DY;
					if ((cam.getRotX() <= 80 && mouseDY < 0) || (cam.getRotX() >= -80 && mouseDY > 0))
					cam.setRotX((cam.getRotX() - mouseDY));
					if (cam.getRotX() > 80) cam.setRotX(80);
					if (cam.getRotX() < -80) cam.setRotX(-80); 
					mouseTimer++;
					if (mouseTimer > 2) {
						Mouse.setCursorPosition(Display.getWidth()/2, Display.getHeight() / 2);
						mouseTimer = 0;
					}
					DX = Mouse.getX();
					DY = Mouse.getY();
	}


	@Override
	public void collision(Entity p) {
		// TODO Auto-generated method stub
		
	}
}
