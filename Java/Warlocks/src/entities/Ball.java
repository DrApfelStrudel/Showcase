package entities;

import java.util.ArrayList;

import org.newdawn.slick.Color;

import basic.Being;
import basic.Collectible;
import basic.Entity;
import basic.Textures;
import basic.Util;
import basic.Vector;

public class Ball implements Collectible {
	
	private float x, y;
	private Vector velocity;
	
	public Ball(float sx, float sy, float v1, float v2) {
		x = sx;
		y = sy;
		velocity = new Vector(v1, v2);
	}

	@Override
	public void Act(ArrayList<Entity> others) {
		x += velocity.getX();
		y += velocity.getY();
		Entity o = Util.getCollision(this, others);
		if (o != null) {
			if (o instanceof Being) {
				Being b = (Being) o;
				b.isHit(velocity, 1);
			}
			others.remove(this); 
			return;
		}
	}

	@Override
	public void Draw(Textures tex) {
		Util.drawTexture(32, 32, x, y, velocity.angle()+90, tex.getTexture("Stuff/Fireball"), Color.white);
	}

	@Override
	public float getX() {
		return x;
	}

	@Override
	public float getY() {
		return y;
	}

	@Override
	public float getWidth() {
		return 32;
	}

	@Override
	public float getHeight() {
		return 32;
	}

}
