import org.lwjgl.opengl.GL11;


public class Particle extends Entity {
	private Point Vector;
	private int range = 200;
	private int timer = 0;
	
	public Particle(float x, float y, float z, int range) {
		super(x,y,z,1);
		speed = 0.2f;
		this.range = range;
		boundPoints = new Point(0.01f,0.01f,0.01f);
		updateBounds();
		Vector = new Point((float)Math.random()/10 - 0.05f,(float)Math.random()/10  - 0.05f,(float)Math.random()/10  - 0.05f);
		immortal = true;
	}

	@Override
	public void Render() {
		TexLoad.tex[1].bind();	
		GL11.glPushMatrix();
		GL11.glColor3f((float)Math.random()/2, (float)Math.random(), (float)Math.random()/2);
		GL11.glTranslatef(x, y, z);
		GL11.glRotatef(-GameBoard.p.getCam().getRotY(), 0, 1, 0);
		GL11.glRotatef(-GameBoard.p.getCam().getRotX(), 1, 0, 0);
		GL11.glBegin(GL11.GL_QUADS);
		GL11.glTexCoord2f(0, 0);
		GL11.glVertex3f(-0.015f, 0.015f, 0);
		GL11.glTexCoord2f(1, 0);
		GL11.glVertex3f(0.015f, 0.015f, 0);
		GL11.glTexCoord2f(1, 1f);
		GL11.glVertex3f(0.015f, -0.015f, 0);
		GL11.glTexCoord2f(0, 1f);
		GL11.glVertex3f(-0.015f, -0.015f, 0);
		GL11.glEnd();
		GL11.glPopMatrix();
	}

	@Override
	public void Update() {

		if (timer++ > range) {
			GameBoard.particles.remove(this);
		}
		x += Vector.x;
		y += Vector.y;
		z += Vector.z;
	}

	@Override
	public void collision(Entity p) {
		// TODO Auto-generated method stub
		
	}

}
