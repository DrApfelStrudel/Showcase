package states;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;

import org.lwjgl.opengl.GL11;
import org.newdawn.slick.Color;

import basic.Board;
import basic.Entity;
import basic.Light;
import basic.State;
import basic.Util;
import entities.Pole;
import entities.Rock;
import entities.Shadow;
import entities.Tree;
import entities.Warlock;

public class GameState implements State {
	
	private Board b;
	private Warlock w;
	private ArrayList<Entity> entities;
	private ArrayList<Light> lights;
	
	public Entity randomEntity() {
		double rand = Math.random();
		if (rand <= 0.1) return new Pole((float)Math.random()*1600-800, (float)Math.random()*1600-800, this);
		if (rand <= 0.5) return new Tree((float)Math.random()*1600-800, (float)Math.random()*1600-800, b.getSounds());
		if (rand <= 0.9) return new Rock((float)Math.random()*1600-800, (float)Math.random()*1600-800, b.getSounds());
		return new Shadow((float) (Math.random()*1600-800), (float) (Math.random()*1600-800));
	}

	public GameState(Board b) {
		this.b = b;
		b.getSounds().fadeMusic("Menu");
		entities = new ArrayList<Entity>();
		lights = new ArrayList<Light>();
		//entities.add(new Tree(0, 200, b.getSounds()));
		
		w = new Warlock(0, 0, b);
		entities.add(w);
		entities.add(new Shadow(100, 100));
		for (int i = 0; i < 200; i++) {
			Entity T = randomEntity();
			if (Util.getCollision(T, entities) == null)
				entities.add(T);
		}
	}
	
	private final int dayLength = 24000;
	private float time = 0;
	private int day = 1;
	
	public void Tick() {	
		if (time >= dayLength) { day++; time = 0; }
		else { time++; }
		if (w.getHP() <= 0) { b.setState(new MenuState(b)); return; }
		b.getKeys().pollInput();
		
		for (int i = entities.size()-1; i >= 0; i--) {
			Entity e = entities.get(i);
			if (Util.vecBetween(w.getX(), w.getY(), e).length() <= Math.max(b.getWidth()*2, b.getHeight()*1.5))
			e.Act(entities);
		}
		
		/* Things in the front should appear in the front!! */
		Collections.sort(entities, new Comparator<Entity>() {
			@Override
			public int compare(Entity a, Entity b) {
				if (a.getY() + a.getHeight()/2 > b.getY() + b.getHeight()/2)
					return -1;
				if (a.getY() + a.getHeight()/2 < b.getY() + b.getHeight()/2)
					return 1;
				return 0;
			} 
			
		});
		//Util.drawSquare(b.getWidth(), b.getHeight(), w.getX(), w.getY(), Color.black);
		
		
		GL11.glBlendFunc(GL11.GL_SRC_ALPHA, GL11.GL_ONE_MINUS_DST_ALPHA);
		Util.drawSquare(b.getWidth(), b.getHeight(), w.getX(), w.getY(), new Color(0,0,0,1-(time <= dayLength/2 ? time : dayLength - time)/(dayLength/2)));
		lightUp();
		GL11.glBlendFunc(GL11.GL_SRC_ALPHA_SATURATE, GL11.GL_ONE);
		
		for (Entity e : entities) {
			if (Util.vecBetween(w.getX(), w.getY(), e).length() <= Math.max(b.getWidth()*2, b.getHeight()*1.5))
			e.Draw(b.getTex());
		}	
		Util.drawSquare(8000, 8000, 0, 0, new Color(0,0.2f,0));
		
	}
	
	public void lightUp() {
		for (Light l : lights) {
			l.lightUp();
		}
	}
	
	public float getCamX() {
		return w.getX()-b.getWidth()/2;
	}
	
	public float getCamY() {
		return w.getY()-b.getHeight()/2;
	}
	
	public void drawBounds(Entity e, Color c) {
		Util.drawSquare(e.getWidth(), e.getHeight(), e.getX(), e.getY(), c);
	}
	
	public Board getBoard() {
		return b;
	}
	
	public void addLight(Light l) {
		lights.add(l);
	}
	
	public void removeLight(Light l) {
		lights.remove(l);
	}
}
