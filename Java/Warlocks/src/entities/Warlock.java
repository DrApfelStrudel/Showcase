package entities;

import java.util.ArrayList;

import org.lwjgl.input.Mouse;
import org.newdawn.slick.Color;

import basic.Being;
import basic.Board;
import basic.Entity;
import basic.Keys;
import basic.Textures;
import basic.Util;
import basic.Vector;

public class Warlock implements Being {

	private float x, y, speed;
	private int HP, MaxHP;
	private Vector knockback;
	private Board b;
	private Keys keys;

	public Warlock(float sx, float sy, Board b) {
		x = sx;
		y = sy;
		speed = 3f;
		knockback = new Vector(0,0);
		this.b = b;
		MaxHP = HP = 5;
		keys = b.getKeys();
	}

	public int getHP() {
		return HP;
	}

	private String[] frames = {/*Idle*/ "Warlock/Down1", 
			/*Down*/ "Warlock/Down1", "Warlock/Down2", "Warlock/Down1", "Warlock/Down3",
			/* Up */ "Warlock/Up1", "Warlock/Up2", "Warlock/Up1", "Warlock/Up3",
			/* Left */ "Warlock/Left1", "Warlock/Left2", "Warlock/Left1", "Warlock/Left3",
			/* Right */ "Warlock/Right1", "Warlock/Right2", "Warlock/Right1", "Warlock/Right3"};
	private int currentFrame = 0;
	private int timer = 0;
	private Color currentColor = Color.white;

	private void incTimer() {
		timer = timer >= 8 ? 0 : timer + 1;
		if (timer == 0) currentColor = Color.white;
	}

	private int getTimer() {
		return timer;
	}

	private void walkRightUp(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 13 && currentFrame > 16)) {
			currentFrame = currentFrame >= 16 ? 13 : (currentFrame < 13 ? 14 : currentFrame + 1);
		}
		x = Util.rightMove(this, others, speed).getF();
		y = Util.topMove(this, others, speed).getF();
	}

	private void walkLeftUp(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 9 && currentFrame > 12)) {
			currentFrame = currentFrame >= 12 ? 9 : (currentFrame < 9 ? 10 : currentFrame + 1);
		}
		x = Util.leftMove(this, others, speed).getF();
		y = Util.topMove(this, others, speed).getF();
	}

	private void walkRightDown(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 13 && currentFrame > 16)) {
			currentFrame = currentFrame >= 16 ? 13 : (currentFrame < 13 ? 14 : currentFrame + 1);
		}
		x = Util.rightMove(this, others, speed).getF();
		y = Util.bottomMove(this, others, speed).getF();
	}

	private void walkLeftDown(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 9 && currentFrame > 12)) {
			currentFrame = currentFrame >= 12 ? 9 : (currentFrame < 9 ? 10 : currentFrame + 1);
		}
		x = Util.leftMove(this, others, speed).getF();
		y = Util.bottomMove(this, others, speed).getF();
	}

	private void walkUp(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 5 && currentFrame > 8)) {
			currentFrame = currentFrame >= 8 ? 5 : (currentFrame < 5 ? 6 : currentFrame + 1);
		}
		y = Util.topMove(this, others, speed).getF();
	}

	private void walkDown(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 1 && currentFrame > 4)) {
			currentFrame = currentFrame >= 4 ? 1 : (currentFrame < 1 ? 2 : currentFrame + 1);
		}
		y = Util.bottomMove(this, others, speed).getF();
	}

	private void walkLeft(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 9 && currentFrame > 12)) {
			currentFrame = currentFrame >= 12 ? 9 : (currentFrame < 9 ? 10 : currentFrame + 1);
		}
		x = Util.leftMove(this, others, speed).getF();
	}

	private void walkRight(ArrayList<Entity> others) {
		if (getTimer() >= 8 || (currentFrame < 13 && currentFrame > 16)) {
			currentFrame = currentFrame >= 16 ? 13 : (currentFrame < 13 ? 14 : currentFrame + 1);
		}
		x = Util.rightMove(this, others, speed).getF();
	}

	private void diminishKnockback() {
		float kX = knockback.getX();
		float kY = knockback.getY();
		knockback.setX(kX >= 0 ? kX - 0.01f - kX/40 < 0 ? 0 : kX - 0.01f - kX/40
				: kX + 0.01f + (-kX)/40 >= 0 ? 0 : kX + 0.01f + (-kX)/40);
		knockback.setY(kY >= 0 ? kY - 0.01f - kY/40 < 0 ? 0 : kY - 0.01f - kY/40
				: kY + 0.01f + (-kY)/40 >= 0 ? 0 : kY + 0.01f + (-kY)/40);
	}

	private void simulateKnockback(ArrayList<Entity> others) {
		if (knockback.getX() != 0 || knockback.getY() != 0) {
			if (knockback.getX() > 0) { x = Util.rightMove(this, others, knockback.getX()).getF(); }
			else { x = Util.leftMove(this, others, -knockback.getX()).getF(); }
			if (knockback.getY() > 0) { y = Util.bottomMove(this, others, knockback.getY()).getF(); }
			else { y = Util.topMove(this, others, -knockback.getY()).getF(); }
			diminishKnockback();
		}
	}

	private void Idle() {
		currentFrame = 0;
	}

	private boolean Walk(ArrayList<Entity> others) {
		if (keys.isDown("W") && keys.isDown("D")) { walkRightUp(others); return true;}
		else if (keys.isDown("W") && keys.isDown("A")) { walkLeftUp(others); return true;}
		else if (keys.isDown("S") && keys.isDown("D")) { walkRightDown(others); return true;}
		else if (keys.isDown("S") && keys.isDown("A")) { walkLeftDown(others); return true;}
		else if (keys.isDown("W")) { walkUp(others); return true; }
		else if (keys.isDown("S")) { walkDown(others); return true; }
		else if (keys.isDown("A")) { walkLeft(others); return true; }
		else if (keys.isDown("D")) { walkRight(others); return true; }
		return false;
	}

	@Override
	public void Act(ArrayList<Entity> others) {
		if (HP == 0) { others.remove(this); return; }
		CD = CD <= 0 ? 0 : CD - 1;
		incTimer();
		simulateKnockback(others);
		if (CD == 0 && Mouse.isButtonDown(0)) { 
			float sx = x + Mouse.getX() - b.getWidth()/2;
			float sy = y + b.getHeight()/2 - Mouse.getY(); 
			float v = sx - x;
			float w = sy - y;
			float y = (float) Math.sqrt(v*v + w*w);
			others.add(new Ball(sx, sy, 10*(v/y), 10*(w/y))); 
			CD = 20;
		}
		if( !Walk(others) ) { Idle(); }
	}

	private int CD = 0;

	@Override
	public void Draw(Textures tex) {
		Util.drawTexture(32, 64, x, y-12, tex.getTexture(frames[currentFrame]), Color.white);
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
		return 16;
	}

	@Override
	public void isHit(Vector knockback, int damage) {
		this.knockback.addVector(knockback);
		HP = HP - damage >= MaxHP ? MaxHP : HP - damage <= 0 ? 0 : HP - damage;
	}
}
