import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;
import java.util.concurrent.CopyOnWriteArrayList;

import org.lwjgl.opengl.GL11;


public class Worm extends Entity {

	private int strength = 10;
	private Tile current;
	private Tile target;
	private float maxSpeed = 0.05f;
	private int type;

	public Worm(Tile t, int type) {
		super(Util.toPos(t.getPos()).x,Util.toPos(t.getPos()).y,Util.toPos(t.getPos()).z, 10);
		boundPoints = new Point(0.5f,0.5f,0.15f);
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		target = t;	
		current = t;
		maxHealth = 10;
		hurtSound = Data.audio[3];
		dieSound = Data.audio[5];
		speed = maxSpeed - (maxSpeed * (health / maxHealth)) + maxSpeed/2; 

		float dist = Util.distanceFrom(getPos(), GameBoard.p.getPos());
		float vol;
		if (dist > 20) {
			vol = 0;
		}
		else {
			vol = 1 - (dist / 20);
		}

		if (type == 1) {
			isRare();
			Data.audio[10].playAsSoundEffect(1f, vol, false);	
		}
		else if (type == 2) {
			isShoot();
			Data.audio[9].playAsSoundEffect(1f, vol, false);
		}
		else if (type == 3) {
			isAttract();
			Data.audio[9].playAsSoundEffect(1f, vol, false);
		}
		else {
			Data.audio[9].playAsSoundEffect(1f, vol, false);
		}
	}

	public void isRare() {
		maxSpeed = 0.2f;
		OriginalColor = new Point(0.25f, 0.25f, 1f);
		strength = 15;
		health = 15;
		maxHealth = 15;
		type = 1;
	}
	
	public void isShoot() {
		OriginalColor = new Point(1,0.25f,0.25f);
		type = 2;
	}
	
	public void isAttract() {
		OriginalColor = new Point(0.75f, 0.1f, 0.5f);
		maxHealth = 5;
		health = 5;
		type = 3;
	}

	public void collision(Entity p) {
		if (p instanceof Player) {
			float b = (float) (Math.cos(Math.toRadians(rotY))*speed);
			float a = (float) (Math.sin(Math.toRadians(rotY))*speed);
			p.health = p.health - strength;
			health = 0;
			p.isHit = true;
			p.knockBack(new Point(b*3,0.1f,-a*3));
		}
		else {
			Point before = getPos();
			float diffX = p.x - getPos().x;
			float diffY = p.y - getPos().y;
			float diffZ = p.z - getPos().z;
			
			float k = (diffX*diffX) + (diffY*diffY) + (diffZ*diffZ);

			diffX = (float) ((float) ((diffX) / Math.sqrt(k)) * speed);
			diffZ = (float) ((float) ((diffZ) / Math.sqrt(k)) * speed);
			
			x -= diffX;  
			if (collideWall()) {
				setPos(before);
			}
			else {
				before = getPos();
			}
			z -= diffZ; 
			if (collideWall()) {
				setPos(before);
			}
		}
	}

	public void nextAnimate() {
		for (int i = 0; i < aniUp.length; i++) {
			if (aniHeight[i] >= 0.025f || aniHeight[i] <= 0) {
				aniUp[i] = !aniUp[i];
			}
			if (aniUp[i]) {
				aniHeight[i] = aniHeight[i] + 0.0025f;
			}
			else {
				aniHeight[i] = aniHeight[i] - 0.0025f;
			}
		}
	}

	public boolean move() {
		float b = (float) (Math.cos(Math.toRadians(rotY))*speed);
		float a = (float) (Math.sin(Math.toRadians(rotY))*speed);
		Point before = getPos();
		z -= a;
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {

				setPos(before);

				bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);

				if (c.getCoords().y-y <= 0.5f) {
					knockVector = new Point(0,0.1f,0);
				}
				else {
					return false;
				}
			}
		}
		before = getPos();
		x += b;
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {

				setPos(before);

				bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);

				if (c.getCoords().y-y <= 0.5f) {
					knockVector = new Point(0,0.1f,0);
				}
				else {
					return false;
				}
			}
		}

		nextAnimate(); 
		
		return true;
	}

	@Deprecated
	public boolean moveX() {
		Point before = getPos();
		x += speed;
		rotY = 0;
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {

				setPos(before);

				bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);

				if (c.getCoords().y-y <= 0.5f) {
					knockVector = new Point(0,0.1f,0);
					return true;
				}
				else {
					return false;
				}
			}
		}
		nextAnimate(); 
		return true;
	}
	
	@Deprecated
	public boolean moveXM() {
		Point before = getPos();
		x -= speed;
		rotY = 180;
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {

				setPos(before);

				bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);

				if (c.getCoords().y-y <= 0.5f) {
					knockVector = new Point(0,0.1f,0);
					return true;
				}
				else {
					return false;
				}
			}
		}
		nextAnimate(); 
		return true;
	}

	@Deprecated
	public boolean moveZ() {
		Point before = getPos();
		z += speed;
		rotY = 270;
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {

				setPos(before);

				bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);

				if (c.getCoords().y-y <= 0.5f) {
					knockVector = new Point(0,0.1f,0);
					return true;
				}
				else {
					return false;
				}
			}
		}
		nextAnimate(); 
		return true;
	}

	@Deprecated
	public boolean moveZM() {
		Point before = getPos();
		rotY = 90;
		z -= speed;
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {

				setPos(before);

				bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);

				if (c.getCoords().y-y <= 0.5f) {
					knockVector = new Point(0,0.1f,0);
					return true;
				}
				else {
					return false;
				}
			}
		}
		nextAnimate(); 
		return true;
	}

	private boolean jump = false;
	
	public void moveToTarget() {
		if (jump && !falling) {
				speed = 0.1f;
				knockVector = new Point(0,0.1f,0);
				jump = false;
		}
		Point p = Util.toPos(target.getPos());
		Point th = getPos();
		int degree = Util.degreeBetween(th, p);
		rotY = degree;

		if (p.x > th.x+0.3f && move()) {

		}
		else if (p.x < th.x-0.3f && move()) {

		}
		else if (p.z > th.z+0.3f && move()) {

		}
		else if (p.z < th.z-0.3f && move()) {

		}
		else if (Math.abs(p.y-th.y)  <= 0.05f){
			if (target.jumpTile == true) {
				jump = true;
			}
			moving = false;
			current = target;
		}
	}

	private float[] aniHeight = {0.025f, 0.0125f, 0, 0.0125f, 0.025f, 0.0125f, 0, 0.0125f};
	private boolean[] aniUp = {true, true, false, false, true, true, false, false};
	private float rotY = 0;

	@Override

	public void Render() {
		if (showName) {
			TexLoad.tex[1].bind();

			GL11.glPushMatrix();
			GL11.glColor3f(1-(health/maxHealth), (health/maxHealth), 0);
			GL11.glTranslatef(x, y, z);
			GL11.glRotatef(-GameBoard.p.getCam().getRotY(), 0, 1, 0);
			GL11.glRotatef(-GameBoard.p.getCam().getRotX(), 1, 0, 0);
			GL11.glBegin(GL11.GL_QUADS);
			GL11.glTexCoord2f(0, 0);
			GL11.glVertex3f(-0.15f, 0.32f, 0);
			GL11.glTexCoord2f(1, 0);
			GL11.glVertex3f(-0.15f+health/maxHealth*0.3f, 0.32f, 0);
			GL11.glTexCoord2f(1, 1f);
			GL11.glVertex3f(-0.15f+health/maxHealth*0.3f, 0.28f, 0);
			GL11.glTexCoord2f(0, 1f);
			GL11.glVertex3f(-0.15f, 0.28f, 0);
			GL11.glEnd();
			GL11.glPopMatrix();
		}

		Cube3D a = new Cube3D(-0.175f,aniHeight[7],-0.01f,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D b = new Cube3D(-0.125f,aniHeight[6],0,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D c = new Cube3D(-0.075f,aniHeight[5],0.01f,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D d = new Cube3D(-0.025f,aniHeight[4],0,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D e = new Cube3D(0.025f,aniHeight[3],-0.01f,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D f = new Cube3D(0.075f,aniHeight[2],0,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D g = new Cube3D(0.125f,aniHeight[1],0.01f,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D h = new Cube3D(0.175f,aniHeight[0],0,0.1f,0.1f,0.1f,color, TexLoad.tex[6]);
		Cube3D i = new Cube3D(0.2251f,aniHeight[0],0,0,0.1f,0.1f,color, TexLoad.tex[7]);
		Cube3D j = new Cube3D(0,0,0,boundPoints.x,boundPoints.z,boundPoints.y,new Point(1f,1f,1f), TexLoad.tex[3]);
		a.setTexBound(new Point(1,1,1));
		b.setTexBound(new Point(1,1,1));
		c.setTexBound(new Point(1,1,1));
		d.setTexBound(new Point(1,1,1));
		e.setTexBound(new Point(1,1,1));
		f.setTexBound(new Point(1,1,1));
		g.setTexBound(new Point(1,1,1));
		h.setTexBound(new Point(1,1,1));
		i.setTexBound(new Point(1,1,1));
		j.setTexBound(new Point(1,1,1));
		GL11.glPushMatrix();
		GL11.glTranslatef(x, y, z);
		GL11.glRotatef(rotY, 0, 1, 0);
		a.draw();
		b.draw();
		c.draw();
		d.draw();
		e.draw();
		f.draw();
		g.draw();
		h.draw();
		i.draw();
		GL11.glPopMatrix();

		if (showHit) {
			GL11.glPushMatrix();
			GL11.glTranslatef(x, y, z);
			j.draw();
			GL11.glPopMatrix();
		}

	}

	private boolean showHit = false;
	private boolean showName = true;

	public boolean canSee(Entity e) {
		float b = (float) (Math.cos(Math.toRadians(rotY))*speed);
		float a = (float) (Math.sin(Math.toRadians(rotY))*speed);
		float la = (e.getPos().x - getPos().x);
		float ha = (e.getPos().y - getPos().y);
		float ba = (e.getPos().z - getPos().z);
		float xa = la/2 + getPos().x;
		float ya = ha/2 + getPos().y;
		float za = ba/2 + getPos().z;
		Cube3D check = new Cube3D(xa,ya,za,Math.abs(la)+0.5f,Math.abs(ha),Math.abs(ba)+0.5f, new Point(0f,1f,0f), TexLoad.tex[1]); 
		check.update();

		for (Cube3D cu : Data.cubes) {

			if (type != 1 && type != 3) {
				if (cu.bounds.collide(check.bounds) && cu.getCoords().y-y >= 0.5f) {
					return false;
				}
			}
			else {
				if (cu.bounds.collide(check.bounds)) {
					return false;
				}
			}
		}

		if (type != 3)
		return standingOn() == GameBoard.p.standingOn();
		else 
		return true;
	}

	public void Grav() {
		falling = true;
		
		Point before = new Point(x,y,z);
		if (downspeed > 0.5f) {
			downspeed = 0.5f;
		}
		y = (y - boundPoints.y/128 - downspeed);
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);

		SPACE : for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {
				if (c.bounds.getPos().y+c.bounds.getSize().y/2-0.1f < y) {
					y = (c.bounds.getPos().y + c.bounds.getSize().y/2 + boundPoints.z/2);
					bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
					knockVector = new Point(knockVector.x, 0, knockVector.z);
					speed = maxSpeed - (maxSpeed * (health / maxHealth)) + maxSpeed/2; 
					falling = false;
					noJump = false;
					downspeed = 0;
					break SPACE;
				}
				else {
					jumping = false;
					noJump = true;
				}
			}
		}

		if (falling) {
			setPos(before);
			y = (y - (downspeed += gravity));
			bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
		}
	}

	int timer = 0;
	int giveUpTimer = 0;
	

	public void bfs(Tile end) {
		Queue<Tile> open = new LinkedList<Tile>();
		ArrayList<Tile> checked = new ArrayList<Tile>();
		open.add(current);
		for (Tile t : Data.waypoints) {
			t.setParent(null);
		}

		while (!open.isEmpty()) {
			Tile now = open.remove();
			checked.add(now);
			if (now == end) {
				if (now.getParent() == null) {
					target = now;
					break;
				}
				while (now.getParent().getParent() != null) {
					now = now.getParent();
				}
				target = now;
			}
			else {
				for (Tile t : now.nb()) {
					if (!open.contains(t) && !checked.contains(t)) {
						t.setParent(now);
						open.add(t);
					}
				}
			}
		}
	}

	public boolean moving = false;
	public boolean isSeen = false;
	
	public void grunt() {

		if ((int)(Math.random()*2000) == 0) {
			knockBack(new Point(0,0.05f,0));
			float dist = Util.distanceFrom(getPos(), GameBoard.p.getPos());
			float vol;
			if (dist > 20) {
				vol = 0;
			}
			else {
				vol = 1f - (dist / 20);
			}
			if (Math.random() < 0.5) {
				Data.audio[7].playAsSoundEffect(1, vol, false);
			}
			else {
				Data.audio[8].playAsSoundEffect(1, vol, false);
			}
		}
	}
	
	public int shootTime = 0;

	@Override
	public void Update() {

		if (Util.distanceFrom(GameBoard.p.getPos(), getPos())  > 200) {
			health = 0;
		}

		Grav();

		if (type == 1) {
			float b = (float) (Math.cos(Math.toRadians(rotY))*0.1);
			float a = (float) (Math.sin(Math.toRadians(rotY))*0.1);
			Point p = new Point(getPos().x+b*5, getPos().y+0.02f, getPos().z-a*5);
			if (GameBoard.p.canSee(p)) {
				isSeen = true;
			}
			else {
				isSeen = false;
				moveToTarget();
			}
		}
		else if (!(canSee(GameBoard.p) && GameBoard.p.health > 0 && type == 3 && Util.distanceFrom(GameBoard.p.getPos(), getPos()) <= 10)){
			moveToTarget();
		}

		grunt();
		
		Tile canSee = null;

		for (Tile s : Data.waypoints) {
			if (s.canSee(GameBoard.p)) {
				if (canSee == null) {
					canSee = s;
				}
				if (Util.distanceFrom(Util.toPos(s.getPos()), GameBoard.p.getPos()) < Util.distanceFrom(Util.toPos(canSee.getPos()), GameBoard.p.getPos())) {
					canSee = s;
				}
			}
		}

		if (canSee(GameBoard.p) && GameBoard.p.health > 0) {
			if (type == 3 && Util.distanceFrom(GameBoard.p.getPos(), getPos()) <= 10) {
				Point before = GameBoard.p.getPos();
				float diffX = GameBoard.p.x - getPos().x;
				float diffY = GameBoard.p.y - getPos().y;
				float diffZ = GameBoard.p.z - getPos().z;
				
				float k = (diffX*diffX) + (diffY*diffY) + (diffZ*diffZ);

				diffX = (float) ((float) ((diffX) / Math.sqrt(k)) * (0.25f * Math.pow(0.575713, Util.distanceFrom(GameBoard.p.getPos(), getPos()))));
				diffY = (float) ((float) ((diffY) / Math.sqrt(k)) * (0.25f * Math.pow(0.575713, Util.distanceFrom(GameBoard.p.getPos(), getPos()))));
				diffZ = (float) ((float) ((diffZ) / Math.sqrt(k)) * (0.25f * Math.pow(0.575713, Util.distanceFrom(GameBoard.p.getPos(), getPos()))));
				
				GameBoard.p.x -= diffX;  
				if (GameBoard.p.collideWall()) {
					GameBoard.p.setPos(before);
				}
				else {
					before = GameBoard.p.getPos();
				}
				GameBoard.p.z -= diffZ; 
				if (GameBoard.p.collideWall()) {
					GameBoard.p.setPos(before);
				}
				GameBoard.p.updateCam();
			}
			moving = false;
			target = Util.toTile(GameBoard.p.getPos());
			if (type == 2) {
				if (Util.distanceFrom(GameBoard.p.getPos(), getPos()) < 2 && shootTime++ > LifeDrain.cd) {
					float b = (float) (Math.cos(Math.toRadians(rotY))*0.1);
					float a = (float) (Math.sin(Math.toRadians(rotY))*0.1);
					Point p = new Point(getPos().x+b*3, getPos().y+0.1f, getPos().z-a*3);
					GameBoard.entities.add(new LifeDrain(p.x,p.y,p.z,rotY-90, 0,this));
					shootTime = 0;
				}
			}
		}
		else if (!moving && canSee != null){
			bfs(canSee);
			moving = true;
		}
		else if (!moving && canSee == null && target.nb().size() > 0) {
			target = current.nb().get((int) (Math.random()*current.nb().size()));
			moving = true;
		}
		
		if (type == 2) {
			for (Entity e : GameBoard.entities) {
				if (!(e instanceof Player) && !(e instanceof Projectile) && e != this && Util.distanceFrom(e.getPos(), getPos()) < 20 && e.health < e.maxHealth && health >= maxHealth / 2) {
					e.health += 0.2f;
					health -= 0.2f;
				}
			}
		}

		if (!target.canSee(this) || giveUpTimer++ == 400){
				Tile closest = Data.waypoints.get(0);
				for (Tile t : Data.waypoints) {
					if (Util.distanceFrom(Util.toPos(closest.getPos()), getPos()) > Util.distanceFrom(Util.toPos(t.getPos()), getPos())) {
						closest = t;
					}

				target = closest;
			}
			moving = true;
			giveUpTimer = 0;
		}

		/*if (isSeen && canSee != null && !canSee(GameBoard.p)) {
			int degree = Util.degreeBetween(Util.toPos(target.getPos()), GameBoard.p.getPos());
			float pla = (360 - GameBoard.p.getCam().getRotY()%360 - 90)%360;
			float deg = Util.degreeDiff(degree, pla);
			if (deg >= 70) {
				moveToTarget();
			}
		}*/

	}

}
