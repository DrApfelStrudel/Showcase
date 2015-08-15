package basic;

import java.util.ArrayList;

public interface Entity {
	// Properties of acting
	public void Act(ArrayList<Entity> others);
	public void Draw(Textures tex);
	
	// Locational Properties (Of bounds not drawings)
	public float getX();
	public float getY();
	public float getWidth();
	public float getHeight();
}
