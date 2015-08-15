import org.lwjgl.opengl.GL11;
import org.newdawn.slick.openal.Audio;


public abstract class Projectile extends Entity {
	protected Entity sender;
	protected Point Vector;
	protected float rotY;
	protected float rotX;
	protected int range = 5;
	protected int timer = 0;
	protected int par = 20;
	protected Audio sound;
	protected Audio hit = null;
	
	public Projectile(float x, float y, float z, float rotY, float rotX, Entity send, Audio sound) {
		super(x,y,z,1);
		speed = 0.2f;
		float c = (float) (Math.sin(Math.toRadians(rotX))*speed);
		float b = (float) (Math.cos(Math.toRadians(rotY))*speed) * (float) Math.cos(Math.toRadians(rotX));
		float a = (float) (Math.sin(Math.toRadians(rotY))*speed) * (float) Math.cos(Math.toRadians(rotX));
		boundPoints = new Point(0.25f,0.25f,0.25f);
		updateBounds();
		Vector = new Point(-a,c,-b);
		this.rotY = rotY;
		this.rotX = rotX;
		sender = send;
		sound.playAsSoundEffect(1, 0.7f, false);
	}
	
	public void hitSound() {
		if (hit != null) {
			float dist = Util.distanceFrom(getPos(), GameBoard.p.getPos());
			float vol;
			if (dist > 100) {
				vol = 0;
			}
			else {
				vol = 1f - (dist / 100);
			}
			hit.playAsSoundEffect(1, vol, false);
		}
	}
	
	@Override
	public void Update() {
		updateBounds();
		if (timer++ > range) {
			if (GameBoard.particles.size() < 1000)
			for (int i = 0; i < par; i++) {
				GameBoard.particles.add(new Particle(x,y,z,50));
			}
			hitSound();
			GameBoard.entities.remove(this);
		}
		for (Cube3D c : Data.cubes) {
			if (this.collide(c.bounds)) {
				if (GameBoard.particles.size() < 1000)
				for (int i = 0; i < par; i++) {
					GameBoard.particles.add(new Particle(x,y,z,50));
				}
				hitSound();
				GameBoard.entities.remove(this);
				break;
			}
		}
		x += Vector.x;
		y += Vector.y;
		z += Vector.z;
	}


	
}	
