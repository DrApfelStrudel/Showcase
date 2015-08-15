package entities;

import java.util.ArrayList;

import org.newdawn.slick.Color;

import basic.Being;
import basic.Entity;
import basic.Sounds;
import basic.Textures;
import basic.Util;
import basic.Vector;

public class Rock implements Being {
	private float x, y;
	private int MaxHP, HP;
	private int hitCD;
	private Color c;
	private Sounds s;
	
	public Rock (float sx, float sy, Sounds s) {
		this.s = s;
		x = sx;
		y = sy;
		MaxHP = HP = 5;
		c = Color.white;
		hitCD = 0;
	}

	@Override
	public void Act(ArrayList<Entity> others) {
		if (HP <= 0) { others.remove(this); return; }
		if (hitCD <= 0) { c = Color.white; } else { c = Color.red; hitCD--; }
		simulateKnockback(others);
	}

	@Override
	public void Draw(Textures tex) {
		Util.drawTexture(32, 32, x, y+5, tex.getTexture("Stuff/Rock"), c);
	}

	@Override
	public float getX() {
		// TODO Auto-generated method stub
		return x;
	}

	@Override
	public float getY() {
		// TODO Auto-generated method stub
		return y;
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
			this.knockback.addVector(knockback);
			HP -= damage;
			hitCD = 10;
			s.playSound("TreeHit");
		}
	}
}
