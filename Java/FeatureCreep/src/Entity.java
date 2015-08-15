import org.newdawn.slick.openal.Audio;


public abstract class Entity {
	protected float x, y, z;
	protected BoundingBox bounds;
	protected Point boundPoints;
	protected boolean falling = false;
	protected boolean jumping = false;
	protected float downspeed = 0;
	public static final float gravity = 0.005f;
	public static final float friction = 20f;
	protected float jumpPower = 0.1f;
	protected float speed = 0.05f;
	protected float health;
	protected float maxHealth;
	protected boolean noJump = false;
	protected Point knockVector;
	protected Audio hurtSound = Data.audio[1];
	protected Audio dieSound = Data.audio[2];
	protected boolean immortal = false;

	public boolean isHit = false;
	protected Point OriginalColor = new Point(1,1,1);
	protected Point color = new Point(1,1,1);

	public Entity(float x, float y, float z, int health) {
		this.x = x;
		this.y = y;
		this.z = z;
		this.health = health;
		maxHealth = health;
		knockVector = new Point(0,0,0);
	}

	public void updateBounds() {
		bounds = new BoundingBox(x,y,z,boundPoints.x,boundPoints.y,boundPoints.z);
	}

	public void knockBack(Point a) {
		knockVector = a;
	}

	public Point getPos() {
		return new Point(x,y,z);
	}

	public void setPos(Point p) {
		x = p.x;
		y = p.y;
		z = p.z;
	}

	public void update() {
		if (!immortal) {
			if (health > 0 && y > -40) {
				Point before = new Point(x,y,z);
				x += knockVector.x;
				y += knockVector.y;
				z += knockVector.z;
				updateBounds();

				Check: {
					for (Cube3D c : Data.cubes) {
						if (bounds.collide(c.bounds)) {
							knockVector = new Point(0,knockVector.y,0);
							setPos(before);
							updateBounds();

							break Check;
						}
					}

					Point antiFric = new Point(knockVector.x/friction, 0, knockVector.z/friction);
					knockVector = new Point(knockVector.x-antiFric.x,knockVector.y-antiFric.y,knockVector.z-antiFric.z);
				}
				Update();

			}
			else {
				health = 0;
				float dist = Util.distanceFrom(getPos(), GameBoard.p.getPos());
				float vol;
				if (dist > 20) {
					vol = 0;
				}
				else {
					vol = 1 - (dist / 20);
				}
				dieSound.playAsSoundEffect(1,vol,false);
				if (GameBoard.particles.size() < 1000)
					for (int i = 0; i < 100; i++) {
						GameBoard.particles.add(new Particle(x,y,z,100));
					}
				GameBoard.entities.remove(this);
			}


			if (isHit) {
				color = new Point(1f,0,0);
				isHit = false;
				hurtSound.playAsSoundEffect(1, 0.4f, false);
			}
			else {
				color = OriginalColor;
			}
		}
		else {
			Update();
		}
		if (health > maxHealth) {
			health = maxHealth;
		}
	}

	public boolean collideWall() {
		for (Cube3D c : Data.cubes) {
			if (bounds.collide(c.bounds)) {
				return true;
			}
		}
		return false;
	}

	public Cube3D standingOn() {
		BoundingBox test = new BoundingBox(x, y - 1f, z, boundPoints.x, 2f, boundPoints.z);
		for (Cube3D cu : Data.cubes) {
			if (test.collide(cu.bounds)) {
				return cu;
			}
		}
		return null;
	}

	public void render() {
		Render();
	}

	public boolean collide(BoundingBox bb) {
		if (bounds.collide(bb)) {
			return true;
		}
		return false;
	}

	public abstract void Render();
	public abstract void Update();
	public abstract void collision(Entity p);
}
