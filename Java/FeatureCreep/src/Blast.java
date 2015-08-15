import org.lwjgl.opengl.GL11;


public class Blast extends Projectile {

	public static final int cd = 20;

	public Blast(float x, float y, float z, float rotY, float rotX, Entity send) {
		super(x,y,z, rotY, rotX, send, Data.audio[13]);
		send.health -= 5;
		range = 80;
		boundPoints = new Point(0.15f,0.01f,0.15f);
		updateBounds();
		par = 300;
		hit = Data.audio[14];
	}

	@Override
	public void collision(Entity p) {
		for (Entity e : GameBoard.entities) {
			if (e != sender && !(e instanceof Projectile)) {
				if (Util.distanceFrom(p.getPos(), e.getPos()) <= 1) {
					if (GameBoard.particles.size() < 1000)
					for (int i = 0; i < par; i++) {
						GameBoard.particles.add(new Particle(x,y,z,50));
					}
					hitSound();
					GameBoard.entities.remove(this);
					e.isHit = true;
					e.health -= 8;
					Point s = new Point(Vector.x*1.8f, 0.1f, Vector.z*1.8f);
					e.knockVector = s;
					GameBoard.entities.remove(this);	
				}
			}
		}
	}

	@Override
	public void Render() {
		Cube3D a = new Cube3D(0,0,0,0.125f,0.125f,0.125f,new Point(1f,1f,1f), TexLoad.tex[12]);
		a.setTexBound(new Point(1,1,1));
		GL11.glPushMatrix();
		GL11.glTranslatef(x, y, z);
		GL11.glRotatef(rotY, 0, 1, 0);
		GL11.glRotatef(rotX, 1, 0, 0);
		a.draw();
		GL11.glPopMatrix();
	}
}
