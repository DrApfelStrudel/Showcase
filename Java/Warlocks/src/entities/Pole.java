package entities;

import java.util.ArrayList;

import org.newdawn.slick.Color;

import states.GameState;
import basic.Being;
import basic.Entity;
import basic.Light;
import basic.Textures;
import basic.Util;
import basic.Vector;

public class Pole implements Being {
	

	private float x, y;
	private int HP;
	private int hitCD;
	private Color c;
	private GameState g;
	private Light l;
	
	public Pole (float sx, float sy, GameState g) {
		x = sx;
		y = sy;
		HP = 5;
		c = Color.white;
		hitCD = 0;
		this.g = g;
	}

	@Override
	public void Act(ArrayList<Entity> others) {
		if (l == null) { l = new Light(this, 150); g.addLight(l); }
		if (HP <= 0) { g.removeLight(l); others.remove(this); return; }
		if (hitCD <= 0) { c = Color.white; } else { c = Color.red; hitCD--; }
		simulateKnockback(others);
	}
	
	private int animFlame = (int) (Math.random() * 32);
	
	public String currentFlame() {
		String dir = "Stuff/Flame/Flame";
		String num = "1";
		if (animFlame >= 24) num = "3";
		else if (animFlame >= 16) num = "1";
		else if (animFlame >= 8) num = "2";
		animFlame = animFlame >= 32 ? 0 : animFlame+1;
		return dir + num;
	}

	@Override
	public void Draw(Textures tex) {
		Util.drawTexture(32, 32, x, y-54, tex.getTexture(currentFlame()), c);
		Util.drawTexture(32, 96, x, y-18, tex.getTexture("Stuff/Pole"), c);
	}

	@Override
	public float getX() {
		// TODO Auto-generated method stub
		return x;
	}

	@Override
	public float getY() {
		// TODO Auto-generated method stub
		return y-10;
	}

	@Override
	public float getWidth() {
		// TODO Auto-generated method stub
		return 32;
	}

	@Override
	public float getHeight() {
		// TODO Auto-generated method stub
		return 20;
	}
	
	private Vector knockback = new Vector(0, 0);

	private void simulateKnockback(ArrayList<Entity> others) {
		
	}
	
	private void diminishKnockback(float r) {

	}

	@Override
	public void isHit(Vector knockback, int damage) {
		if (hitCD <= 0) {
			HP -= damage;
			hitCD = 10;
			this.knockback.addVector(knockback);
			g.getBoard().getSounds().playSound("TreeHit");
		}
	}

}
