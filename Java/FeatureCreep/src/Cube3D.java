import static org.lwjgl.opengl.GL11.GL_TEXTURE_2D;

import java.nio.FloatBuffer;
import java.util.ArrayList;

import org.lwjgl.BufferUtils;
import org.lwjgl.opengl.GL11;
import org.lwjgl.opengl.GL15;
import org.lwjgl.opengl.GL15.*;
import org.newdawn.slick.opengl.Texture;


public class Cube3D {
	protected float x;
	protected float y;
	protected float z;
	private float l;
	protected float h;
	private float b;
	private float ta;
	private float tb;
	public boolean showBounds = false;
	private float tc;
	private boolean removeBack = false;
	public Point color;
	public BoundingBox bounds;
	private Texture tex;
	public boolean normal = true;

	public Cube3D(float x, float y, float z, float l, float b, float h, Point color, Texture tex) {
		this.x = x;
		this.y = y;
		this.z = z;
		this.l = l;
		this.h = b;
		this.b = h;
		this.tex = tex;
		this.color = color;
		bounds = new BoundingBox(x, y, z, l, b, h);

			ta = l;
			tb = h;
			tc = b;


	}
	
	public boolean collide(Cube3D c) {
		return c.bounds.collide(bounds);
	}
	
	public void setTexBound(Point p) {
		ta = p.x;
		tb = p.y;
		tc = p.z;
	}
	
	public void update() {
		bounds = new BoundingBox(x, y, z, l, b, h);
	}
	
	public void toggleRemoveBack() {
		removeBack = !removeBack;
	}
	
	public Point getCoords() {
		return new Point(x,y,z);
	}
	
	public Point getSize() {
		return new Point(l,h,b);
	}

	public void draw() {
		
		if (!normal) {
			ta = tb = tc = 1;
		}
		
		GL11.glColor3f(color.x, color.y, color.z);
		tex.bind();
		
		if (showBounds) {
			Cube3D j = new Cube3D(bounds.getPos().x,bounds.getPos().y,bounds.getPos().z,bounds.getSize().x,bounds.getSize().y,bounds.getSize().z,new Point(1f,1f,1f), TexLoad.tex[3]);
			j.showBounds = false;
			j.draw();
		}
		else {
		GL11.glPushMatrix();
		GL11.glTranslatef(x, y, z);
		GL11.glTexParameteri(GL_TEXTURE_2D, GL11.GL_TEXTURE_MAG_FILTER, GL11.GL_NEAREST);
		GL11.glBegin(GL11.GL_QUADS);
			
		//BOTTOM
		GL11.glTexCoord2f(0, 0);
		GL11.glVertex3f(l/2, -h/2, -b/2);
		GL11.glTexCoord2f(ta, 0);
		GL11.glVertex3f(-l/2, -h/2, -b/2);
		GL11.glTexCoord2f(ta, tb);
		GL11.glVertex3f(-l/2, -h/2, b/2);
		GL11.glTexCoord2f(0, tb);
		GL11.glVertex3f(l/2, -h/2, b/2);
		
		//TOP
		GL11.glTexCoord2f(0, 0);
		GL11.glVertex3f(-l/2, h/2, -b/2);
		GL11.glTexCoord2f(ta, 0);
		GL11.glVertex3f(l/2, h/2, -b/2);
		GL11.glTexCoord2f(ta, tb);
		GL11.glVertex3f(l/2, h/2, b/2);
		GL11.glTexCoord2f(0, tb);
		GL11.glVertex3f(-l/2, h/2, b/2);

		//Sides
		
		//RIGHT
		GL11.glTexCoord2f(0, 0);
		GL11.glVertex3f(-l/2, h/2, -b/2);
		
		GL11.glTexCoord2f(tb, 0);
		GL11.glVertex3f(-l/2, h/2, b/2);
		
		GL11.glTexCoord2f(tb, tc);
		GL11.glVertex3f(-l/2, -h/2, b/2);
		
		GL11.glTexCoord2f(0, tc);
		GL11.glVertex3f(-l/2, -h/2, -b/2);
		
		//LEFT
		GL11.glTexCoord2f(0, 0);
		GL11.glVertex3f(l/2, h/2, b/2);
		
		GL11.glTexCoord2f(tb, 0);
		GL11.glVertex3f(l/2, h/2, -b/2);
		
		GL11.glTexCoord2f(tb, tc);
		GL11.glVertex3f(l/2, -h/2, -b/2);
		
		GL11.glTexCoord2f(0, tc);
		GL11.glVertex3f(l/2, -h/2, b/2);
		
		//FRONT
		GL11.glTexCoord2f(0, 0);
		GL11.glVertex3f(l/2, h/2, -b/2);
		
		GL11.glTexCoord2f(ta, 0);
		GL11.glVertex3f(-l/2, h/2, -b/2);
		
		GL11.glTexCoord2f(ta, tc);
		GL11.glVertex3f(-l/2, -h/2, -b/2);
		
		GL11.glTexCoord2f(0, tc);
		GL11.glVertex3f(l/2, -h/2, -b/2);

		//BACK
		if (!removeBack) {
		GL11.glTexCoord2f(0, 0);
		GL11.glVertex3f(-l/2, h/2, b/2);
		
		GL11.glTexCoord2f(ta, 0);
		GL11.glVertex3f(l/2, h/2, b/2);
		
		GL11.glTexCoord2f(ta, tc);
		GL11.glVertex3f(l/2, -h/2, b/2);
		
		GL11.glTexCoord2f(0, tc);
		GL11.glVertex3f(-l/2, -h/2, b/2);
		}
		
		GL11.glEnd();
		
		GL11.glPopMatrix();
		}
	}
}
