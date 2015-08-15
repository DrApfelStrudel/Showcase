import org.lwjgl.opengl.GL11;


public class LifeDrain extends Projectile {
	
	public static final int cd = 5;
	
	public LifeDrain(float x, float y, float z, float rotY, float rotX, Entity send) {
		super(x,y,z, rotY, rotX, send, Data.audio[6]);
	}

	@Override
	public void collision(Entity p) {
		if (p != sender && !(p instanceof Projectile)) {
			p.isHit = true;
			p.health -= 1;
			sender.health += 2f;
			Point s = new Point(Vector.x*0.2f, 0, Vector.z*0.2f);
			p.knockVector = s;
			GameBoard.entities.remove(this);
		}
	}
	
	@Override
	public void Render() {
		Cube3D a = new Cube3D(0,0,0,0.005f,0.05f,0.25f,new Point(1f,1f,1f), TexLoad.tex[3]);
		a.setTexBound(new Point(1,1,1));
		GL11.glPushMatrix();
		GL11.glTranslatef(x, y, z);
		GL11.glRotatef(rotY, 0, 1, 0);
		GL11.glRotatef(rotX, 1, 0, 0);
		a.draw();
		GL11.glPopMatrix();
	}
}
