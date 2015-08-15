import java.nio.FloatBuffer;

import org.lwjgl.BufferUtils;
import org.lwjgl.opengl.GL11;
import org.lwjgl.opengl.GL15;


public class Square {
	
	private FloatBuffer vertexData;
	private FloatBuffer colorData;
	private int vboVertexHandle;
	private int vboColorHandle;
	
	public Square(Point a, Point b, Point c, Point d, Point color) {
		vertexData = BufferUtils.createFloatBuffer(12);
        vertexData.put(new float[]{a.x, a.y, a.z, b.x, b.y, b.z, c.x, c.y, c.z, d.x, d.y, d.z});
        vertexData.flip();

        colorData = BufferUtils.createFloatBuffer(12);
        colorData.put(new float[]{color.x, color.y, color.z,
        						  color.x, color.y, color.z,
        						  color.x, color.y, color.z,
        						  color.x, color.y, color.z});
        colorData.flip();
        
        vboVertexHandle = GL15.glGenBuffers();
        GL15.glBindBuffer(GL15.GL_ARRAY_BUFFER, vboVertexHandle);
        GL15.glBufferData(GL15.GL_ARRAY_BUFFER, vertexData, GL15.GL_STATIC_DRAW);
        GL15.glBindBuffer(GL15.GL_ARRAY_BUFFER, 0);

        vboColorHandle = GL15.glGenBuffers();
        GL15.glBindBuffer(GL15.GL_ARRAY_BUFFER, vboColorHandle);
        GL15.glBufferData(GL15.GL_ARRAY_BUFFER, colorData, GL15.GL_STATIC_DRAW);
        GL15.glBindBuffer(GL15.GL_ARRAY_BUFFER, 0);
	}
	
	public void draw() {
        GL15.glBindBuffer(GL15.GL_ARRAY_BUFFER, vboVertexHandle);
        GL11.glVertexPointer(3, GL11.GL_FLOAT, 0, 0L);

        GL15.glBindBuffer(GL15.GL_ARRAY_BUFFER, vboColorHandle);
        GL11.glColorPointer(3, GL11.GL_FLOAT, 0, 0L);

        GL11.glEnableClientState(GL11.GL_VERTEX_ARRAY);
        GL11.glEnableClientState(GL11.GL_COLOR_ARRAY);
        GL11.glDrawArrays(GL11.GL_QUADS, 0, 4);
        GL11.glDisableClientState(GL11.GL_COLOR_ARRAY);
        GL11.glDisableClientState(GL11.GL_VERTEX_ARRAY);
	}
}
