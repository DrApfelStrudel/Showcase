package basic;
import java.util.ArrayList;

import org.lwjgl.opengl.GL11;
import org.newdawn.slick.Color;
import org.newdawn.slick.opengl.Texture;

public class Util {
	
	public static Vector vecBetween(float x, float y, Entity e) {
		return new Vector(e.getX() - x, e.getY() - y);
	}
	
	public static Vector vecBetween(float x1, float y1, float x2, float y2) {
		return new Vector(x2 - x1, y2 - y1);
	}
	
	public static boolean ballCollision(float x1, float y1, float r1, float x2, float y2, float r2) {
		float xd = x1 - x2;
	    float yd = y1 - y2;
	    float distSqr = (float) Math.sqrt(xd * xd + yd * yd);
	    float sumRadius = r1 + r2;

	    return distSqr <= sumRadius;
	}
	
	public static boolean onlyYCollision (Entity e, Entity o) {
		float r1t = e.getY() - e.getHeight()/2;		
		float r1b = e.getY() + e.getHeight()/2;
		float r2t = o.getY() - o.getHeight()/2;			
		float r2b = o.getY() + o.getHeight()/2;
		return !(r1b < r2t || r1t > r2b);
	}
	
	public static boolean onlyXCollision (Entity e, Entity o) {
		float r1t = e.getX() - e.getWidth()/2;		
		float r1b = e.getX() + e.getWidth()/2;
		float r2t = o.getX() - o.getWidth()/2;			
		float r2b = o.getX() + o.getWidth()/2;
		return !(r1b < r2t || r1t > r2b);
	}
	
	
	
	public static boolean collision(Entity e, Entity o) {
		return e != o && onlyYCollision(e, o) && onlyXCollision(e, o);
	}

	public static Entity getCollision(Entity e, ArrayList<Entity> others) {
		for (Entity o : others) {
			if (o != e) {
				if (collision(e, o)) {
					return o;
				}
			}
		}
		return null;
	}
	
	public static float leftDistance(Entity e, Entity o) {
		float oR = o.getX() + o.getWidth()/2;
		float eL = e.getX() - e.getWidth()/2;
		return eL - oR;
	}
	
	public static float rightDistance(Entity e, Entity o) {
		float oL = o.getX() - o.getWidth()/2;
		float eR = e.getX() + e.getWidth()/2;
		return oL - eR;
	}
	
	public static float upDistance(Entity e, Entity o) {
		float oB = o.getY() + o.getHeight()/2;
		float eT = e.getY() - e.getHeight()/2;
		return eT - oB;
	}
	
	public static float downDistance(Entity e, Entity o) {
		float oT = o.getY() - o.getHeight()/2;
		float eB = e.getY() + e.getHeight()/2;
		return oT - eB;
	}
	
	public static Entity getClosestTopCollision(Entity e, ArrayList<Entity> others, float Tdist) {
		Entity closest = null;
		for (Entity o : others) {
			if (o != e && !(o instanceof Collectible)) {
			   float dist = upDistance(e, o);
			   if (dist <= Tdist && dist >= 0 && onlyXCollision(e, o)) {
				   closest = closest == null ? o : 
					   		 dist < upDistance(e, closest) ? o : closest;
			   }
			}
		}
		return closest;
	}
	
	public static Entity getClosestBottomCollision(Entity e, ArrayList<Entity> others, float Bdist) {
		Entity closest = null;
		for (Entity o : others) {
			if (o != e && !(o instanceof Collectible)) {
			   float dist = downDistance(e, o);
			   if (dist <= Bdist && dist >= 0 && onlyXCollision(e, o)) {
				   closest = closest == null ? o : 
					   		 dist < downDistance(e, closest) ? o : closest;
			   }
			}
		}
		return closest;
	}
	
	public static Entity getClosestLeftCollision(Entity e, ArrayList<Entity> others, float Ldist) {
		Entity closest = null;
		for (Entity o : others) {
			if (o != e && !(o instanceof Collectible)) {
			   float dist = leftDistance(e, o);
			   if (dist <= Ldist && dist >= 0 && onlyYCollision(e, o)) {
				   closest = closest == null ? o : 
					   		 dist < leftDistance(e, closest) ? o : closest;
			   }
			}
		}
		return closest;
	}
	
	public static Entity getClosestRightCollision(Entity e, ArrayList<Entity> others, float Rdist) {
		Entity closest = null;
		for (Entity o : others) {
			if (o != e && !(o instanceof Collectible)) {
			   float dist = rightDistance(e, o);
			   if (dist <= Rdist && dist >= 0 && onlyYCollision(e, o)) {
				   closest = closest == null ? o : 
					   		 dist < rightDistance(e, closest) ? o : closest;
			   }
			}
		}
		return closest;
	}
	
	public static float leftPoint(Entity e, Entity o) {
		return o.getX() + o.getWidth()/2 + e.getWidth()/2 + 0.001f;
	}
	
	public static Pair<Float, Entity> leftMove(Entity e, ArrayList<Entity> others, float LDist) {
		Entity closest = getClosestLeftCollision(e, others, LDist);
		if (closest != null) return new Pair<Float, Entity>(leftPoint(e, closest), closest);
		else			     return new Pair<Float, Entity>(e.getX() - LDist, null);
	}
	
	public static float rightPoint(Entity e, Entity o) {
		return o.getX() - o.getWidth()/2 - e.getWidth()/2 - 0.001f;
	}
	
	public static Pair<Float, Entity> rightMove(Entity e, ArrayList<Entity> others, float RDist) {
		Entity closest = getClosestRightCollision(e, others, RDist);
		if (closest != null) return new Pair<Float, Entity>(rightPoint(e, closest), closest);
		else			     return new Pair<Float, Entity>(e.getX() + RDist, null);
	}
	
	public static float topPoint(Entity e, Entity o) {
		return o.getY() + o.getHeight()/2 + e.getHeight()/2 + 0.001f;
	}
	
	public static Pair<Float, Entity> topMove(Entity e, ArrayList<Entity> others, float TDist) {
		Entity closest = getClosestTopCollision(e, others, TDist);
		if (closest != null) return new Pair<Float, Entity>(topPoint(e, closest), closest);
		else			     return new Pair<Float, Entity>(e.getY() - TDist, null);
	}
	
	public static float bottomPoint(Entity e, Entity o) {
		return o.getY() - o.getHeight()/2 - e.getHeight()/2 - 0.001f;
	}
	
	public static Pair<Float, Entity> bottomMove(Entity e, ArrayList<Entity> others, float BDist) {
		Entity closest = getClosestBottomCollision(e, others, BDist);
		if (closest != null) return new Pair<Float, Entity>(bottomPoint(e, closest), closest);
		else			     return new Pair<Float, Entity>(e.getY() + BDist, null);
	}

	public static void write(String s, int size, float x, float y, Color c, Textures tex) {
		float nx = x - size*1.2f*(((float) s.length())/2f)+size*0.6f;
		for (int i = 0; i < s.length(); i++) {
			if (Character.toUpperCase(s.charAt(i)) == 'Q')
			drawTexture(size, size*1.9f, nx, y+size*0.45f, tex.getTexture("Fonts/Q"), c);
			else if (s.charAt(i) == '.')
			drawSquare(size/3f, size/3f, nx-size/3f, y + size/3f, c);
			else if (s.charAt(i) == ',')
			drawSquare(size/3f, size/1.5f, nx-size/3f, y + size/1.5f, c);
			else if (s.charAt(i) != ' ')
			drawTexture(size, size, nx, y, tex.getTexture("Fonts/"+Character.toUpperCase(s.charAt(i))), c);
			else
			drawSquare(size, size, nx, y, Color.transparent);		
			nx += size*1.2f;
		}
	}
	
	public static void drawTexture(float width, float height, float x, float y, float rotation, Texture t, Color c) {
		GL11.glPushMatrix();
		GL11.glTranslatef(x,y,0);
		GL11.glRotatef(rotation, 0, 0, 1);

		GL11.glEnable(GL11.GL_TEXTURE_2D);    
		c.bind();
		t.bind();
		GL11.glTexParameteri(GL11.GL_TEXTURE_2D, GL11.GL_TEXTURE_MIN_FILTER, GL11.GL_NEAREST);
		GL11.glTexParameteri(GL11.GL_TEXTURE_2D, GL11.GL_TEXTURE_MAG_FILTER, GL11.GL_NEAREST);
		
		GL11.glBegin(GL11.GL_QUADS);
		    GL11.glTexCoord2f(0,0);
			GL11.glVertex2f(-width/2, -height/2);
			GL11.glTexCoord2f(1,0);
			GL11.glVertex2f(width/2, -height/2);
			GL11.glTexCoord2f(1,1);
			GL11.glVertex2f(width/2, height/2);
			GL11.glTexCoord2f(0,1);
			GL11.glVertex2f(-width/2, height/2);
	    GL11.glEnd();
	    
	    GL11.glPopMatrix();
	}
	
	public static void drawTexture(float width, float height, float x, float y, Texture t, Color c) {
		GL11.glPushMatrix();
		GL11.glTranslatef(x,y,0);

		GL11.glEnable(GL11.GL_TEXTURE_2D);    
		c.bind();
		t.bind();
		GL11.glTexParameteri(GL11.GL_TEXTURE_2D, GL11.GL_TEXTURE_MIN_FILTER, GL11.GL_NEAREST);
		GL11.glTexParameteri(GL11.GL_TEXTURE_2D, GL11.GL_TEXTURE_MAG_FILTER, GL11.GL_NEAREST);
		
		GL11.glBegin(GL11.GL_QUADS);
		    GL11.glTexCoord2f(0,0);
			GL11.glVertex2f(-width/2, -height/2);
			GL11.glTexCoord2f(1,0);
			GL11.glVertex2f(width/2, -height/2);
			GL11.glTexCoord2f(1,1);
			GL11.glVertex2f(width/2, height/2);
			GL11.glTexCoord2f(0,1);
			GL11.glVertex2f(-width/2, height/2);
	    GL11.glEnd();
	    
	    GL11.glPopMatrix();
	    GL11.glDisable(GL11.GL_TEXTURE_2D); 
	}
	
	public static void drawSquare (float width, float height, float x, float y, Color c) {
		GL11.glDisable(GL11.GL_TEXTURE_2D);    
		c.bind();
		GL11.glTexParameteri(GL11.GL_TEXTURE_2D, GL11.GL_TEXTURE_MIN_FILTER, GL11.GL_NEAREST);
		GL11.glTexParameteri(GL11.GL_TEXTURE_2D, GL11.GL_TEXTURE_MAG_FILTER, GL11.GL_NEAREST);
		
		GL11.glBegin(GL11.GL_QUADS);
		    GL11.glTexCoord2f(0,0);
			GL11.glVertex2f(x-width/2, y-height/2);
			GL11.glTexCoord2f(1,0);
			GL11.glVertex2f(x+width/2, y-height/2);
			GL11.glTexCoord2f(1,1);
			GL11.glVertex2f(x+width/2, y+height/2);
			GL11.glTexCoord2f(0,1);
			GL11.glVertex2f(x-width/2, y+height/2);
	    GL11.glEnd();
	}
	
	public static void drawGradientCircle(float x, float y, int slices, float radius, Color c)
    {
		  GL11.glPushMatrix();
		  GL11.glTranslatef(x, y, 0);
          float incr = (float) (2 * Math.PI / slices);

          GL11.glBegin(GL11.GL_TRIANGLE_FAN);

                GL11.glColor4f(c.r, c.g, c.b, 0.03f);
                GL11.glVertex2f(0.0f, 1f);

                
                for(int i = 0; i < slices; i++)
                {
                      float angle = incr * i;

                      float xx = (float) Math.cos(angle) * radius;
                      float yx = (float) Math.sin(angle) * radius;
                      GL11.glColor4f(0f,0, 0, 0.1f);
                      GL11.glVertex2f(xx, yx);
                }

                GL11.glVertex2f(radius, 0.0f);

          GL11.glEnd();
          GL11.glPopMatrix();
    }
	
}
