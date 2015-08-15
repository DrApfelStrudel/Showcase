package basic;

import states.MenuState;


public class Board {
	
	private State currentState;
	private Textures tex;
	private Keys keys;
	private Sounds sounds;
	private float width, height;
	
	public Board(float width, float height) {
		tex = new Textures();
		keys = new Keys();
		sounds = new Sounds();
		currentState = new MenuState(this);	
		this.width = width;
		this.height = height;
	}
	
	public Textures getTex() {
		return tex;
	}
	
	public Keys getKeys() {
		return keys;
	}
	
	public Sounds getSounds() {
		return sounds;
	}
	
	public void Tick() {
		keys.pollInput();
		currentState.Tick();
		
	}
	
	public void setState(State s) {
		currentState = s;
	}
	
	public float getCamX() {
		return currentState.getCamX();
	}
	
	public float getCamY() {
		return currentState.getCamY();
	}
	
	public float getWidth() {
		return width;
	}
	
	public float getHeight() {
		return height;
	}

}
